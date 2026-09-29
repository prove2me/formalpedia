-- Prove2me | solution 1 for FourExp.extrapolation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T14:36:23.978933+00:00
-- url     : https://prove2.me/submissions/60352656-5967-4be9-9f9f-73104f05745e

import Mathlib
import Theorems.Thm_FourExp_cauchy_estimate_with_zeros

open Finset

namespace FourExpExtra

/-- The Cauchy estimate with the zero count replaced by `|P| · n₀`. -/
lemma zeros_bound (F : ℂ → ℂ) (hF : Differentiable ℂ F) (w : ℂ) (ρ R M : ℝ) (hρ : 0 ≤ ρ)
    (hR : ρ + 1 < R) (P : Finset ℂ) (hP : ∀ z ∈ P, ‖z - w‖ ≤ ρ)
    (hM : ∀ z : ℂ, ‖z - w‖ = R → ‖F z‖ ≤ M) (n₀ : ℕ)
    (hvan : ∀ z ∈ P, ∀ m < n₀, iteratedDeriv m F z = 0) (hr : (ρ + 1) / (R - ρ) ≤ 1) (s : ℕ) :
    ‖iteratedDeriv s F w‖ ≤ (s.factorial : ℝ) * (R / (R - 1)) * ((ρ + 1) / (R - ρ)) ^ (P.card * n₀) * M := by
  have hR0 : 0 < R := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (w + R) (by simp [abs_of_pos hR0]))
  have hr0 : 0 ≤ (ρ + 1) / (R - ρ) := div_nonneg (by linarith) (by linarith)
  have hRR : 0 ≤ R / (R - 1) := div_nonneg hR0.le (by linarith)
  by_cases htop : ∃ z ∈ P, analyticOrderAt F z = ⊤
  · obtain ⟨z, -, hz⟩ := htop
    have h0 : F = 0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z fun z₀ => hF.analyticAt z₀).1 hz
    subst h0
    have : iteratedDeriv s (0 : ℂ → ℂ) w = 0 := by
      rw [show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, iteratedDeriv_const]; split_ifs <;> rfl
    rw [this, norm_zero]
    positivity
  simp only [not_exists, not_and] at htop
  have hC := FourExp.cauchy_estimate_with_zeros F hF w ρ R M hρ hR P hP hM s
  have hle : P.card * n₀ ≤ ∑ z ∈ P, analyticOrderNatAt F z := by
    have : P.card * n₀ = ∑ z ∈ P, n₀ := by rw [Finset.sum_const, smul_eq_mul]
    rw [this]
    refine Finset.sum_le_sum fun z hz => ?_
    have h1 : (n₀ : ℕ∞) ≤ analyticOrderAt F z :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hF.analyticAt z)).2 (hvan z hz)
    rw [← Nat.cast_analyticOrderNatAt (htop z hz)] at h1
    exact_mod_cast h1
  refine hC.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hr0 hr hle) (by positivity)) hM0)

lemma floor_ge_half {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff x).2 hx
  by_cases hx2 : x < 2
  · linarith
  · linarith

lemma norm_natCast_sub_le {a a' t : ℕ} (ha : a < t) (ha' : a' < t) : ‖(a' : ℂ) - a‖ ≤ t := by
  have : ‖(a' : ℂ) - a‖ = |(a' : ℝ) - a| := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  rw [this, abs_sub_le_iff]
  have h1 : (a : ℝ) < t := by exact_mod_cast ha
  have h2 : (a' : ℝ) < t := by exact_mod_cast ha'
  have h3 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ a' := Nat.cast_nonneg _
  constructor <;> linarith

theorem grid_estimate (x₁ x₂ y₁ y₂ : ℂ) (hy : LinearIndependent ℚ ![y₁, y₂]) (K : ℝ)
    (N S t₁ t₂ : ℕ) (hN : 2 ≤ N) (c : Fin S → Fin (2 * N) → Fin (2 * N) → ℂ)
    (hc : ∀ i j k', ‖c i j k'‖ ≤ Real.exp K)
    (hvan : ∀ a b m : ℕ, a < t₁ → b < t₂ → m < S →
      iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
        c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
        ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0)
    (ρ Z : ℝ) (hρ : ρ = 14 * (t₁ * ‖y₁‖ + t₂ * ‖y₂‖)) (hZ : Z = (ρ + 1) * (N + 1))
    (s a b : ℕ) (ha : a < 14 * t₁) (hb : b < 14 * t₂) :
    ‖iteratedDeriv s (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
        c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
        ((a : ℂ) * y₁ + (b : ℂ) * y₂)‖
      ≤ (s.factorial : ℝ) * ((ρ + 1) * N / ((ρ + 1) * N - 1)) * (1 / ((N : ℝ) - 1)) ^ (t₁ * t₂ * S) *
        (S * (2 * N) * (2 * N) * Real.exp K * Z ^ S * Real.exp (2 * N * (‖x₁‖ + ‖x₂‖) * Z)) := by
  set F : ℂ → ℂ := fun z : ℂ => ∑ i : Fin S, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
        c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z) with hFdef
  have hF : Differentiable ℂ F := by rw [hFdef]; fun_prop
  set w : ℂ := (a : ℂ) * y₁ + (b : ℂ) * y₂ with hw
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  set R : ℝ := (ρ + 1) * N with hR
  have hRgt : ρ + 1 < R := by rw [hR]; nlinarith
  set P : Finset ℂ := ((range t₁) ×ˢ (range t₂)).image (fun p => (p.1 : ℂ) * y₁ + (p.2 : ℂ) * y₂) with hP
  have hcard : P.card = t₁ * t₂ := by
    rw [hP, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, Finset.card_range]
    rintro ⟨p1, p2⟩ - ⟨q1, q2⟩ - hpq
    simp only at hpq
    have h := (LinearIndependent.pair_iff.1 hy) ((p1 : ℚ) - q1) ((p2 : ℚ) - q2) (by
      simp only [Rat.smul_def]; push_cast; linear_combination hpq)
    have e1 : (p1 : ℚ) = q1 := sub_eq_zero.1 h.1
    have e2 : (p2 : ℚ) = q2 := sub_eq_zero.1 h.2
    simp only [Prod.mk.injEq]
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
  have hPw : ∀ z ∈ P, ‖z - w‖ ≤ ρ := by
    intro z hz
    rw [hP, Finset.mem_image] at hz
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hz
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    have e : (a' : ℂ) * y₁ + (b' : ℂ) * y₂ - w = ((a' : ℂ) - a) * y₁ + ((b' : ℂ) - b) * y₂ := by
      rw [hw]; ring
    rw [e, hρ]
    have h1 := norm_natCast_sub_le (by omega : a < 14 * t₁) (by omega : a' < 14 * t₁)
    have h2 := norm_natCast_sub_le (by omega : b < 14 * t₂) (by omega : b' < 14 * t₂)
    push_cast at h1 h2
    calc ‖((a' : ℂ) - a) * y₁ + ((b' : ℂ) - b) * y₂‖
        ≤ ‖(a' : ℂ) - a‖ * ‖y₁‖ + ‖(b' : ℂ) - b‖ * ‖y₂‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ 14 * t₁ * ‖y₁‖ + 14 * t₂ * ‖y₂‖ := by gcongr
      _ = 14 * (t₁ * ‖y₁‖ + t₂ * ‖y₂‖) := by ring
  have hwρ : ‖w‖ ≤ ρ := by
    rw [hw, hρ]
    have h1 : (a : ℝ) ≤ 14 * t₁ := by exact_mod_cast ha.le
    have h2 : (b : ℝ) ≤ 14 * t₂ := by exact_mod_cast hb.le
    calc ‖(a : ℂ) * y₁ + (b : ℂ) * y₂‖ ≤ a * ‖y₁‖ + b * ‖y₂‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]; simp
      _ ≤ 14 * t₁ * ‖y₁‖ + 14 * t₂ * ‖y₂‖ := by gcongr
      _ = 14 * (t₁ * ‖y₁‖ + t₂ * ‖y₂‖) := by ring
  have hZ1 : 1 ≤ Z := by rw [hZ]; nlinarith
  have hM : ∀ z : ℂ, ‖z - w‖ = R →
      ‖F z‖ ≤ S * (2 * N) * (2 * N) * Real.exp K * Z ^ S * Real.exp (2 * N * (‖x₁‖ + ‖x₂‖) * Z) := by
    intro z hz
    have hzZ : ‖z‖ ≤ Z := by
      have := norm_le_insert' z w
      rw [hZ]; nlinarith
    have hterm : ∀ (i : Fin S) (j k' : Fin (2 * N)),
        ‖c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)‖
          ≤ Real.exp K * Z ^ S * Real.exp (2 * N * (‖x₁‖ + ‖x₂‖) * Z) := by
      intro i j k'
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
      have hj : ((j : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast j.2.le
      have hk : ((k' : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast k'.2.le
      have hre : ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z).re ≤ 2 * N * (‖x₁‖ + ‖x₂‖) * Z := by
        refine (Complex.re_le_norm _).trans ?_
        rw [norm_mul]
        have hb1 : ‖((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂‖ ≤ 2 * N * (‖x₁‖ + ‖x₂‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
          nlinarith [norm_nonneg x₁, norm_nonneg x₂]
        exact mul_le_mul hb1 hzZ (norm_nonneg _) (by positivity)
      have hpow : ‖z‖ ^ (i : ℕ) ≤ Z ^ S :=
        (pow_le_pow_left₀ (norm_nonneg _) hzZ _).trans (pow_le_pow_right₀ hZ1 i.2.le)
      have := Real.exp_le_exp.2 hre
      exact mul_le_mul (mul_le_mul (hc i j k') hpow (by positivity) (by positivity)) this
        (by positivity) (by positivity)
    calc ‖F z‖ ≤ ∑ i : Fin S, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
          Real.exp K * Z ^ S * Real.exp (2 * N * (‖x₁‖ + ‖x₂‖) * Z) := by
          rw [hFdef]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' _ => hterm i j k')
      _ = S * (2 * N) * (2 * N) * Real.exp K * Z ^ S * Real.exp (2 * N * (‖x₁‖ + ‖x₂‖) * Z) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hratio : (ρ + 1) / (R - ρ) ≤ 1 / ((N : ℝ) - 1) := by
    rw [div_le_div_iff₀ (by rw [hR]; nlinarith) (by linarith)]
    rw [hR]; nlinarith
  have hr1 : (ρ + 1) / (R - ρ) ≤ 1 := hratio.trans (by rw [div_le_one (by linarith)]; linarith)
  have hvan' : ∀ z ∈ P, ∀ m < S, iteratedDeriv m F z = 0 := by
    intro z hz m hm
    rw [hP, Finset.mem_image] at hz
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hz
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    exact hvan a' b' m hab.1 hab.2 hm
  have key := zeros_bound F hF w ρ R _ hρ0 hRgt P hPw hM S hvan' hr1 s
  rw [hcard] at key
  refine key.trans ?_
  have hM0 : 0 ≤ S * (2 * N) * (2 * N) * Real.exp K * Z ^ S * Real.exp (2 * N * (‖x₁‖ + ‖x₂‖) * Z) := by
    positivity
  have hRR : 0 ≤ R / (R - 1) := div_nonneg (by linarith) (by linarith)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) hratio _) (by positivity)) hM0

lemma log_nat_facts {N : ℕ} (hN : 3 ≤ N) :
    1 ≤ Real.log N ∧ Real.log N ≤ N ∧ Real.log N / 2 ≤ Real.log ((N : ℝ) - 1) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  · have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N); linarith
  · have h : (N : ℝ) ≤ ((N : ℝ) - 1) ^ 2 := by nlinarith
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow] at this
    push_cast at this
    linarith

/-- Shared facts about `L = log N` and `q = √L`. -/
lemma q_facts {N : ℕ} (hN : 3 ≤ N) :
    1 ≤ Real.sqrt (Real.log N) ∧ Real.sqrt (Real.log N) * Real.sqrt (Real.log N) = Real.log N ∧
      Real.sqrt (Real.log N) ≤ N := by
  obtain ⟨hL1, hLN, -⟩ := log_nat_facts hN
  have hq1 : 1 ≤ Real.sqrt (Real.log N) := Real.one_le_sqrt.2 hL1
  have hqq := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ Real.log N)
  refine ⟨hq1, hqq, ?_⟩
  have : Real.sqrt (Real.log N) ≤ Real.log N := by
    linear_combination mul_le_mul_of_nonneg_left hq1 (by linarith : (0 : ℝ) ≤ Real.sqrt (Real.log N)) + hqq
  linarith

lemma bound_A1 (N S sd : ℕ) (hN : 3 ≤ N) (hS1 : 1 ≤ S) (hsd : sd ≤ S)
    (hSu : (S : ℝ) * Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2) :
    (sd.factorial : ℝ) ≤ Real.exp (2 * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) := by
  obtain ⟨hq1, hqq, -⟩ := q_facts hN
  have hS0 : (1 : ℝ) ≤ S := by exact_mod_cast hS1
  have hSN : (S : ℝ) ≤ N ^ 2 := by
    linear_combination mul_le_mul_of_nonneg_left hq1 (by linarith : (0 : ℝ) ≤ S) + hSu
  have hnat : sd.factorial ≤ S ^ S :=
    (Nat.factorial_le_pow sd).trans ((Nat.pow_le_pow_left hsd sd).trans (Nat.pow_le_pow_right hS1 hsd))
  have hcast : (sd.factorial : ℝ) ≤ (S : ℝ) ^ S := by exact_mod_cast hnat
  refine hcast.trans ?_
  rw [← Real.exp_log (by linarith : (0 : ℝ) < S), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have hlogS : Real.log S ≤ 2 * Real.log N := by
    have := Real.log_le_log (by linarith) hSN
    rwa [Real.log_pow] at this
  have e1 : (S : ℝ) * Real.log S ≤ S * (2 * Real.log N) := mul_le_mul_of_nonneg_left hlogS (by linarith)
  have e2 : Real.sqrt (Real.log N) * ((S : ℝ) * Real.sqrt (Real.log N)) ≤ Real.sqrt (Real.log N) * N ^ 2 :=
    mul_le_mul_of_nonneg_left hSu (by linarith)
  linear_combination e1 + 2 * e2 - 2 * (S : ℝ) * hqq

lemma bound_A2 (ρ : ℝ) (hρ0 : 0 ≤ ρ) (N : ℕ) (hN : 3 ≤ N) :
    (ρ + 1) * N / ((ρ + 1) * N - 1) ≤ Real.exp 1 := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hR : 3 ≤ (ρ + 1) * N := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  have := Real.add_one_le_exp 1
  nlinarith

lemma bound_A3 (N S t₁ t₂ : ℕ) (hN : 3 ≤ N)
    (hSl : (N : ℝ) ^ 2 ≤ 2 * (S * Real.sqrt (Real.log N)))
    (h1l : (N : ℝ) ≤ 2 * (t₁ * Real.sqrt (Real.log N)))
    (h2l : (N : ℝ) * Real.sqrt (Real.log N) ≤ 2 * t₂) :
    (1 / ((N : ℝ) - 1)) ^ (t₁ * t₂ * S) ≤ Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log N)) / 16)) := by
  obtain ⟨-, -, hLN1⟩ := log_nat_facts hN
  obtain ⟨hq1, hqq, -⟩ := q_facts hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N - 1 := by linarith
  rw [one_div, ← Real.exp_log hpos, ← Real.exp_neg, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  set q := Real.sqrt (Real.log N)
  set n : ℝ := ((t₁ * t₂ * S : ℕ) : ℝ) with hn
  have hn' : n = (t₁ : ℝ) * t₂ * S := by rw [hn]; push_cast; ring
  have f1 : (N : ℝ) * (N * q) ≤ (2 * (t₁ * q)) * (2 * t₂) :=
    mul_le_mul h1l h2l (by positivity) (by positivity)
  have f2 : ((N : ℝ) * (N * q)) * N ^ 2 ≤ ((2 * (t₁ * q)) * (2 * t₂)) * (2 * (S * q)) :=
    mul_le_mul f1 hSl (by positivity) (by positivity)
  have hn4 : (N : ℝ) ^ 4 * q ≤ 8 * n * (q * q) := by
    rw [hn']; linear_combination f2
  have hn0 : (0 : ℝ) ≤ n := by rw [hn]; exact Nat.cast_nonneg _
  have g1 : n * (Real.log N / 2) ≤ n * Real.log ((N : ℝ) - 1) := mul_le_mul_of_nonneg_left hLN1 hn0
  rw [hqq] at hn4
  linear_combination g1 + hn4 / 16

lemma bound_B1 (N S : ℕ) (hN : 3 ≤ N) (hSu : (S : ℝ) * Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2) :
    (S : ℝ) * (2 * N) * (2 * N) ≤ Real.exp (7 * ((N : ℝ) ^ 3 * Real.sqrt (Real.log N))) := by
  obtain ⟨hL1, hLN, -⟩ := log_nat_facts hN
  obtain ⟨hq1, hqq, hqN⟩ := q_facts hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set q := Real.sqrt (Real.log N)
  have hSN : (S : ℝ) ≤ N ^ 2 := by
    linear_combination mul_le_mul_of_nonneg_left hq1 (Nat.cast_nonneg (α := ℝ) S) + hSu
  have h4 : (S : ℝ) * (2 * N) * (2 * N) ≤ 4 * (N : ℝ) ^ 4 := by
    have := mul_le_mul_of_nonneg_right hSN (by positivity : (0 : ℝ) ≤ 4 * N ^ 2)
    linear_combination this
  refine h4.trans ?_
  have e4 : (4 : ℝ) * (N : ℝ) ^ 4 = Real.exp (Real.log 4 + 4 * Real.log N) := by
    rw [Real.exp_add, Real.exp_log (by norm_num),
      show (4 : ℝ) * Real.log N = Real.log ((N : ℝ) ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [e4]
  apply Real.exp_le_exp.2
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith
  have hL3 : Real.log N ≤ (N : ℝ) ^ 3 := by nlinarith
  have k1 := mul_le_mul hL3 hq1 zero_le_one (by positivity)
  have k2 := mul_le_mul hN3 hq1 zero_le_one (by positivity)
  linarith

lemma bound_Z (Y ρ Z : ℝ) (hY : 0 ≤ Y) (hρ0 : 0 ≤ ρ) (N : ℕ) (hN : 3 ≤ N)
    (hρ : ρ ≤ 14 * Y * N * Real.sqrt (Real.log N)) (hZ : Z = (ρ + 1) * (N + 1)) :
    1 ≤ Z ∧ Z ≤ 2 * (14 * Y + 1) * (N : ℝ) ^ 3 ∧ Z ≤ 2 * (14 * Y + 1) * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N)) := by
  obtain ⟨hq1, -, hqN⟩ := q_facts hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set q := Real.sqrt (Real.log N)
  have hNq : (1 : ℝ) ≤ N * q := by nlinarith
  have hρ1 : ρ + 1 ≤ (14 * Y + 1) * (N * q) := by nlinarith
  have hN1 : (N : ℝ) + 1 ≤ 2 * N := by linarith
  have hZ2 : Z ≤ 2 * (14 * Y + 1) * ((N : ℝ) ^ 2 * q) := by
    rw [hZ]
    have := mul_le_mul hρ1 hN1 (by linarith) (by positivity)
    linear_combination this
  refine ⟨by rw [hZ]; nlinarith, ?_, hZ2⟩
  have : (N : ℝ) ^ 2 * q ≤ N ^ 3 := by
    have := mul_le_mul_of_nonneg_left hqN (by positivity : (0 : ℝ) ≤ N ^ 2); linear_combination this
  have h14 : 0 ≤ 2 * (14 * Y + 1) := by positivity
  linear_combination hZ2 + mul_le_mul_of_nonneg_left this h14

lemma bound_B2 (Y Z : ℝ) (hY : 0 ≤ Y) (N S : ℕ) (hN : 3 ≤ N)
    (hSu : (S : ℝ) * Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2) (hZ1 : 1 ≤ Z)
    (hZle : Z ≤ 2 * (14 * Y + 1) * (N : ℝ) ^ 3) :
    Z ^ S ≤ Real.exp ((Real.log (2 * (14 * Y + 1)) + 3) * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) := by
  obtain ⟨hq1, hqq, -⟩ := q_facts hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← Real.exp_log (by linarith : (0 : ℝ) < Z), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  set q := Real.sqrt (Real.log N)
  set C := Real.log (2 * (14 * Y + 1))
  have hC : 0 ≤ C := Real.log_nonneg (by linarith)
  have hlogZ : Real.log Z ≤ C + 3 * Real.log N := by
    have := Real.log_le_log (by linarith) hZle
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have e1 : (S : ℝ) * Real.log Z ≤ S * (C + 3 * Real.log N) := mul_le_mul_of_nonneg_left hlogZ hS0
  have e2 : (S : ℝ) ≤ N ^ 2 * q := by
    have a1 := mul_le_mul_of_nonneg_left hq1 hS0
    have a2 := mul_le_mul_of_nonneg_left hq1 (by positivity : (0 : ℝ) ≤ N ^ 2)
    linear_combination a1 + hSu + a2
  have e3 := mul_le_mul_of_nonneg_right e2 hC
  have e4 : q * ((S : ℝ) * q) ≤ q * N ^ 2 := mul_le_mul_of_nonneg_left hSu (by linarith)
  linear_combination e1 + e3 + 3 * e4 - 3 * (S : ℝ) * hqq

lemma bound_B3 (X Y Z : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (N : ℕ)
    (hZ2 : Z ≤ 2 * (14 * Y + 1) * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) :
    2 * (N : ℝ) * X * Z ≤ 4 * X * (14 * Y + 1) * ((N : ℝ) ^ 3 * Real.sqrt (Real.log N)) := by
  have := mul_le_mul_of_nonneg_left hZ2 (by positivity : (0 : ℝ) ≤ 2 * N * X)
  linear_combination this

lemma numbers (X Y κ : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hκ : 0 < κ) (N S t₁ t₂ sd : ℕ) (hN : 3 ≤ N)
    (hbig : 32 * (13 + κ + Real.log (2 * (14 * Y + 1)) + 4 * X * (14 * Y + 1)) ≤ N)
    (hS1 : 1 ≤ S) (hsd : sd ≤ S)
    (hSu : (S : ℝ) * Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2)
    (hSl : (N : ℝ) ^ 2 ≤ 2 * (S * Real.sqrt (Real.log N)))
    (h1l : (N : ℝ) ≤ 2 * (t₁ * Real.sqrt (Real.log N)))
    (h2l : (N : ℝ) * Real.sqrt (Real.log N) ≤ 2 * t₂)
    (ρ Z : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 14 * Y * N * Real.sqrt (Real.log N)) (hZ : Z = (ρ + 1) * (N + 1)) :
    (sd.factorial : ℝ) * ((ρ + 1) * N / ((ρ + 1) * N - 1)) * (1 / ((N : ℝ) - 1)) ^ (t₁ * t₂ * S) *
        (S * (2 * N) * (2 * N) * Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) * Z ^ S *
          Real.exp (2 * N * X * Z))
      ≤ Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log N)) / 32)) := by
  have hA1 := bound_A1 N S sd hN hS1 hsd hSu
  have hA2 := bound_A2 ρ hρ0 N hN
  have hA3 := bound_A3 N S t₁ t₂ hN hSl h1l h2l
  have hB1 := bound_B1 N S hN hSu
  obtain ⟨hZ1, hZ3, hZ2⟩ := bound_Z Y ρ Z hY hρ0 N hN hρ hZ
  have hB2 := bound_B2 Y Z hY N S hN hSu hZ1 hZ3
  have hB3 := bound_B3 X Y Z hX hY N hZ2
  obtain ⟨hq1, -, -⟩ := q_facts hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set q := Real.sqrt (Real.log N) with hq
  set C := Real.log (2 * (14 * Y + 1)) with hCdef
  have hC : 0 ≤ C := Real.log_nonneg (by linarith)
  have hRpos : 0 < (ρ + 1) * N - 1 := by nlinarith
  have hN3q : 1 ≤ (N : ℝ) ^ 3 * q := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith
    nlinarith
  have hN2q : (N : ℝ) ^ 2 * q ≤ N ^ 3 * q := by
    have : (N : ℝ) ^ 2 ≤ N ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hfin : 2 * ((N : ℝ) ^ 2 * q) + 1 + -(((N : ℝ) ^ 4 * q) / 16) + (7 * ((N : ℝ) ^ 3 * q) +
      κ * ((N : ℝ) ^ 2 * q) + (C + 3) * ((N : ℝ) ^ 2 * q) +
      4 * X * (14 * Y + 1) * ((N : ℝ) ^ 3 * q)) ≤ -(((N : ℝ) ^ 4 * q) / 32) := by
    have g1 := mul_le_mul_of_nonneg_left hN2q (by linarith : (0 : ℝ) ≤ 5 + κ + C)
    have g2 := mul_le_mul_of_nonneg_right hbig (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3 * q)
    have e : (N : ℝ) * ((N : ℝ) ^ 3 * q) = (N : ℝ) ^ 4 * q := by ring
    rw [e] at g2
    linear_combination g1 + hN3q + g2 / 32
  have h1 : (sd.factorial : ℝ) * ((ρ + 1) * N / ((ρ + 1) * N - 1)) * (1 / ((N : ℝ) - 1)) ^ (t₁ * t₂ * S)
      ≤ Real.exp (2 * ((N : ℝ) ^ 2 * q)) * Real.exp 1 * Real.exp (-(((N : ℝ) ^ 4 * q) / 16)) := by
    have hr0 : 0 ≤ (ρ + 1) * N / ((ρ + 1) * N - 1) := div_nonneg (by positivity) hRpos.le
    have hp0 : 0 ≤ (1 / ((N : ℝ) - 1)) ^ (t₁ * t₂ * S) := pow_nonneg (div_nonneg zero_le_one (by linarith)) _
    exact mul_le_mul (mul_le_mul hA1 hA2 hr0 (Real.exp_pos _).le) hA3 hp0 (by positivity)
  have h2 : (S : ℝ) * (2 * N) * (2 * N) * Real.exp (κ * ((N : ℝ) ^ 2 * q)) * Z ^ S * Real.exp (2 * N * X * Z)
      ≤ Real.exp (7 * ((N : ℝ) ^ 3 * q)) * Real.exp (κ * ((N : ℝ) ^ 2 * q)) *
          Real.exp ((C + 3) * ((N : ℝ) ^ 2 * q)) * Real.exp (4 * X * (14 * Y + 1) * ((N : ℝ) ^ 3 * q)) := by
    have hS0 : (0 : ℝ) ≤ S * (2 * N) * (2 * N) := by positivity
    refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hB1 (Real.exp_pos _).le) hB2
      (pow_nonneg (by linarith) _) (by positivity)) (Real.exp_le_exp.2 hB3) (Real.exp_pos _).le (by positivity)
  have h0 : 0 ≤ (S : ℝ) * (2 * N) * (2 * N) * Real.exp (κ * ((N : ℝ) ^ 2 * q)) * Z ^ S *
      Real.exp (2 * N * X * Z) := by
    have : (0 : ℝ) ≤ Z ^ S := pow_nonneg (by linarith) _
    positivity
  calc _ ≤ (Real.exp (2 * ((N : ℝ) ^ 2 * q)) * Real.exp 1 * Real.exp (-(((N : ℝ) ^ 4 * q) / 16))) *
          (Real.exp (7 * ((N : ℝ) ^ 3 * q)) * Real.exp (κ * ((N : ℝ) ^ 2 * q)) *
          Real.exp ((C + 3) * ((N : ℝ) ^ 2 * q)) * Real.exp (4 * X * (14 * Y + 1) * ((N : ℝ) ^ 3 * q))) :=
        mul_le_mul h1 h2 h0 (by positivity)
    _ = Real.exp (2 * ((N : ℝ) ^ 2 * q) + 1 + -(((N : ℝ) ^ 4 * q) / 16) + (7 * ((N : ℝ) ^ 3 * q) +
      κ * ((N : ℝ) ^ 2 * q) + (C + 3) * ((N : ℝ) ^ 2 * q) +
      4 * X * (14 * Y + 1) * ((N : ℝ) ^ 3 * q))) := by simp only [Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.2 hfin

end FourExpExtra

theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (hy : LinearIndependent ℚ ![y₁, y₂]) (κ : ℝ) (hκ : 0 < κ) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ c : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → ℂ,
      (∀ i j k', ‖c i j k'‖ ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) →
      (∀ a b m : ℕ, a < ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → m < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
        iteratedDeriv m (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0) →
      ∀ s : ℕ, s < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2 → ∀ a b : ℕ, a < 14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < 14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ →
        ‖iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂)‖
          ≤ Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log (N : ℝ))) / κ')) := by
  set X := ‖x₁‖ + ‖x₂‖ with hXdef
  set Y := ‖y₁‖ + ‖y₂‖ with hYdef
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  refine ⟨32, by norm_num,
    max 3 ⌈32 * (13 + κ + Real.log (2 * (14 * Y + 1)) + 4 * X * (14 * Y + 1))⌉₊,
    fun N hN c hc hvan sd hsd a b ha hb => ?_⟩
  have hN3 : 3 ≤ N := by omega
  have hbig : 32 * (13 + κ + Real.log (2 * (14 * Y + 1)) + 4 * X * (14 * Y + 1)) ≤ N := by
    have h1 := Nat.le_ceil (32 * (13 + κ + Real.log (2 * (14 * Y + 1)) + 4 * X * (14 * Y + 1)))
    have h2 : ⌈32 * (13 + κ + Real.log (2 * (14 * Y + 1)) + 4 * X * (14 * Y + 1))⌉₊ ≤ N := by omega
    exact h1.trans (by exact_mod_cast h2)
  obtain ⟨hL1, hLN, -⟩ := FourExpExtra.log_nat_facts hN3
  obtain ⟨hq1, hqq, hqN⟩ := FourExpExtra.q_facts hN3
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hqpos : 0 < Real.sqrt (Real.log N) := by linarith
  -- floors
  have hSu : (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) * Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2 := by
    rw [← le_div_iff₀ hqpos]; exact Nat.floor_le (by positivity)
  have hNq1 : 1 ≤ (N : ℝ) / Real.sqrt (Real.log N) := by rw [le_div_iff₀ hqpos]; linarith
  have hN2q1 : 1 ≤ (N : ℝ) ^ 2 / Real.sqrt (Real.log N) := by rw [le_div_iff₀ hqpos]; nlinarith
  have hNq1' : 1 ≤ (N : ℝ) * Real.sqrt (Real.log N) := by nlinarith
  have hSl : (N : ℝ) ^ 2 ≤ 2 * (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * Real.sqrt (Real.log N)) := by
    have := FourExpExtra.floor_ge_half hN2q1
    rw [div_div, div_le_iff₀ (by positivity)] at this
    linarith
  have hS1 : 1 ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ := (Nat.one_le_floor_iff _).2 hN2q1
  have h1l : (N : ℝ) ≤ 2 * (⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ * Real.sqrt (Real.log N)) := by
    have := FourExpExtra.floor_ge_half hNq1
    rw [div_div, div_le_iff₀ (by positivity)] at this
    linarith
  have h2l : (N : ℝ) * Real.sqrt (Real.log N) ≤ 2 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ := by
    have := FourExpExtra.floor_ge_half hNq1'
    linarith
  have h1u : (⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ N * Real.sqrt (Real.log N) := by
    have h := Nat.floor_le (by positivity : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (Real.log N))
    have : (N : ℝ) / Real.sqrt (Real.log N) ≤ N := div_le_self (by positivity) hq1
    nlinarith
  have h2u : (⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ N * Real.sqrt (Real.log N) :=
    Nat.floor_le (by positivity)
  have hρ : 14 * ((⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) * ‖y₁‖ +
      (⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) * ‖y₂‖) ≤ 14 * Y * N * Real.sqrt (Real.log N) := by
    have e1 := mul_le_mul_of_nonneg_right h1u (norm_nonneg y₁)
    have e2 := mul_le_mul_of_nonneg_right h2u (norm_nonneg y₂)
    rw [hYdef]; linear_combination 14 * e1 + 14 * e2
  have hg := FourExpExtra.grid_estimate x₁ x₂ y₁ y₂ hy (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))
    N _ _ _ (by omega) c hc hvan _ _ rfl rfl sd a b ha hb
  refine hg.trans ?_
  exact FourExpExtra.numbers X Y κ hX hY hκ N _ _ _ sd hN3 hbig hS1 (by omega) hSu hSl h1l h2l _ _
    (by positivity) hρ rfl
