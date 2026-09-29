-- Prove2me | solution 1 for Gelbart.hecke_automorphic_of_nice
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T11:16:26.889644+00:00
-- url     : https://prove2.me/submissions/e7f0cfed-1693-4c29-82f6-8e6fdda0b20e

import Mathlib
import Definitions.Def_Gelbart_hecke_conditions
set_option autoImplicit false


open Complex Real Filter Topology Set MeasureTheory Asymptotics

namespace Gelbart

/-- the summands of `heckeForm` on the imaginary axis -/
noncomputable def hterm (a : ℕ → ℂ) (h : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  a n * ((Real.exp (-(2 * π * n / h) * x) : ℝ) : ℂ)

lemma heckeForm_I_mul (a : ℕ → ℂ) (h x : ℝ) :
    heckeForm a h (I * x) = ∑' n, hterm a h n x := by
  unfold heckeForm hterm
  congr 1
  funext n
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- polynomial bound on the coefficients valid for every index -/
lemma coeff_bound (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (hgrowth : HeckeCoeffGrowth a c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ m : ℕ, ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + ‖a 0‖ := by
  obtain ⟨K, hK⟩ := hgrowth
  refine ⟨max K 0, le_max_right _ _, Nat.ceil c, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (0 : ℝ) ≤ max K 0 * ((0 : ℕ) : ℝ) ^ Nat.ceil c := by
      apply mul_nonneg (le_max_right _ _); positivity
    linarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 := hK n hn
    have h2 : (n : ℝ) ^ c ≤ (n : ℝ) ^ (Nat.ceil c : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil c)
    rw [Real.rpow_natCast] at h2
    have h3 : K * (n : ℝ) ^ c ≤ max K 0 * (n : ℝ) ^ Nat.ceil c := by
      calc K * (n : ℝ) ^ c ≤ max K 0 * (n : ℝ) ^ c := by
            apply mul_le_mul_of_nonneg_right (le_max_left _ _); positivity
        _ ≤ max K 0 * (n : ℝ) ^ Nat.ceil c := by
            apply mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    have := norm_nonneg (a 0)
    linarith

lemma summable_bound (K A : ℝ) (m : ℕ) {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => (K * (n : ℝ) ^ m + A) * Real.exp (-(α * n))) := by
  have hr : ‖Real.exp (-α)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one m hr
  have h2 := summable_geometric_of_norm_lt_one hr
  have h3 := (h1.mul_left K).add (h2.mul_left A)
  refine h3.congr fun n => ?_
  rw [← Real.exp_nat_mul]
  ring_nf

/-- the Hecke form on the imaginary axis -/
noncomputable def phi (a : ℕ → ℂ) (h : ℝ) (x : ℝ) : ℂ := heckeForm a h (I * x)

lemma norm_hterm (a : ℕ → ℂ) (h : ℝ) (n : ℕ) (x : ℝ) :
    ‖hterm a h n x‖ = ‖a n‖ * Real.exp (-(2 * π * n / h) * x) := by
  unfold hterm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma hterm_le (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {δ x : ℝ} (hδ : δ ≤ x) (n : ℕ) :
    ‖hterm a h n x‖ ≤ (K * (n : ℝ) ^ m + A) * Real.exp (-((2 * π * δ / h) * n)) := by
  rw [norm_hterm]
  apply mul_le_mul (hK n) _ (Real.exp_pos _).le ((norm_nonneg _).trans (hK n))
  apply Real.exp_le_exp.2
  have : 0 ≤ 2 * π * n / h := by positivity
  have : (2 * π * δ / h) * n = (2 * π * n / h) * δ := by ring
  nlinarith

lemma phi_eq_tsum (a : ℕ → ℂ) (h x : ℝ) : phi a h x = ∑' n, hterm a h n x :=
  heckeForm_I_mul a h x

lemma summable_hterm (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {x : ℝ} (hx : 0 < x) :
    Summable (fun n => hterm a h n x) := by
  apply Summable.of_norm_bounded (summable_bound K A m (by positivity : 0 < 2 * π * x / h))
  intro n
  exact hterm_le a h hh K A m hK (le_refl x) n

lemma continuousOn_phi (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) : ContinuousOn (phi a h) (Ioi 0) := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  have hcont : ContinuousOn (fun y => ∑' n, hterm a h n y) (Ici (x / 2)) := by
    apply continuousOn_tsum (u := fun n : ℕ => (K * (n : ℝ) ^ m + A) *
      Real.exp (-((2 * π * (x / 2) / h) * n)))
    · intro n
      unfold hterm
      fun_prop
    · exact summable_bound K A m (by positivity)
    · intro n y hy
      exact hterm_le a h hh K A m hK hy n
  have : ContinuousAt (fun y => ∑' n, hterm a h n y) x :=
    hcont.continuousAt (Ici_mem_nhds (by linarith))
  have heq : phi a h = fun y => ∑' n, hterm a h n y := funext (phi_eq_tsum a h)
  rw [heq]
  exact this.continuousWithinAt

lemma phi_sub_bound (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) :
    ∃ S : ℝ, ∀ x : ℝ, 1 ≤ x → ‖phi a h x - a 0‖ ≤ S * Real.exp (-(2 * π / h) * (x - 1)) := by
  set β := 2 * π / h with hβ
  have hβ0 : 0 < β := by positivity
  set u : ℕ → ℝ := fun n => (K * ((n + 1 : ℕ) : ℝ) ^ m + A) * Real.exp (-(β * (n + 1 : ℕ)))
  have hu : Summable u := by
    have := summable_bound K A m hβ0
    exact (summable_nat_add_iff 1).2 this
  refine ⟨∑' n, u n, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hs := summable_hterm a h hh K A m hK hx0
  rw [phi_eq_tsum, hs.tsum_eq_zero_add]
  have h0 : hterm a h 0 x = a 0 := by simp [hterm]
  rw [h0, add_sub_cancel_left]
  have hs' : Summable (fun n => hterm a h (n + 1) x) := (summable_nat_add_iff 1).2 hs
  have hb : ∀ n : ℕ, ‖hterm a h (n + 1) x‖ ≤ u n * Real.exp (-β * (x - 1)) := by
    intro n
    rw [norm_hterm]
    simp only [u]
    refine le_trans ?_ (le_of_eq (mul_assoc _ _ _).symm)
    apply mul_le_mul ((hK (n + 1))) _ (Real.exp_pos _).le
      ((norm_nonneg _).trans (hK (n + 1)))
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have : -(2 * π * ((n + 1 : ℕ) : ℝ) / h) * x = -(β * ((n + 1 : ℕ) : ℝ)) * x := by
      rw [hβ]; ring
    rw [this]
    push_cast
    nlinarith [mul_nonneg (mul_nonneg hβ0.le (Nat.cast_nonneg n)) (sub_nonneg.2 hx)]
  calc ‖∑' n, hterm a h (n + 1) x‖ ≤ ∑' n, u n * Real.exp (-β * (x - 1)) :=
        tsum_of_norm_bounded (hu.mul_right _).hasSum hb
    _ = (∑' n, u n) * Real.exp (-β * (x - 1)) := tsum_mul_right

lemma phi_isBigO (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) (r : ℝ) :
    (fun x => phi a h x - a 0) =O[atTop] (fun x : ℝ => x ^ r) := by
  obtain ⟨S, hS⟩ := phi_sub_bound a h hh K A m hK
  have hβ0 : 0 < 2 * π / h := by positivity
  have h1 : (fun x => phi a h x - a 0) =O[atTop] (fun x => Real.exp (-(2 * π / h) * x)) := by
    apply IsBigO.of_bound (|S| * Real.exp (2 * π / h))
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖phi a h x - a 0‖ ≤ S * Real.exp (-(2 * π / h) * (x - 1)) := hS x hx
      _ ≤ |S| * Real.exp (-(2 * π / h) * (x - 1)) := by
          gcongr; exact le_abs_self S
      _ = |S| * Real.exp (2 * π / h) * Real.exp (-(2 * π / h) * x) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop hβ0 r).isBigO

lemma phi_feq (a : ℕ → ℂ) (h k : ℝ) (C : ℂ) (hA : HeckeAutomorphic a h k C) {x : ℝ}
    (hx : 0 < x) : phi a h (1 / x) = (C * ↑(x ^ k)) • phi a h x := by
  have hz : 0 < (I * (x : ℂ)).im := by simp [hx]
  have := hA (I * x) hz
  unfold phi
  have e1 : (-1 / (I * (x : ℂ))) = I * ((1 / x : ℝ) : ℂ) := by
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast
    field_simp
    rw [Complex.I_sq]
  have e2 : (I * (x : ℂ) / I) ^ (k : ℂ) = ((x ^ k : ℝ) : ℂ) := by
    rw [mul_div_cancel_left₀ _ Complex.I_ne_zero, Complex.ofReal_cpow hx.le]
  rw [← e1, this, e2, smul_eq_mul]

/-- coefficients with the constant term removed -/
noncomputable def aa (a : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else a n

/-- frequencies -/
noncomputable def pp (h : ℝ) (n : ℕ) : ℝ := 2 * π * n / h

lemma hasSum_phi_sub (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n => aa a n * (Real.exp (-pp h n * t) : ℂ)) (phi a h t - a 0) := by
  have hs := (summable_hterm a h hh K A m hK ht).hasSum
  rw [← phi_eq_tsum] at hs
  have h2 := hs.sub (hasSum_ite_eq 0 (a 0))
  have e : (fun n => aa a n * (Real.exp (-pp h n * t) : ℂ))
      = (fun b => hterm a h b t - if b = 0 then a 0 else 0) := by
    funext n
    unfold aa hterm pp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn.ne']
  rw [e]; exact h2

lemma summable_aa_div (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) {σ : ℝ} (hσ : c + 1 < σ) :
    Summable (fun n => ‖aa a n‖ / (pp h n) ^ σ) := by
  obtain ⟨K, hK⟩ := hgrowth
  have hσ0 : 0 < σ := by linarith
  set B := |K| * (h / (2 * π)) ^ σ
  have hs : Summable (fun n : ℕ => B * (n : ℝ) ^ (c - σ)) :=
    (Real.summable_nat_rpow.2 (by linarith)).mul_left B
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by unfold pp; positivity) _))
    (fun n => ?_) hs
  unfold aa pp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
  · simp only [hn.ne', if_false]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hp : (2 * π * n / h) ^ σ = (2 * π / h) ^ σ * (n : ℝ) ^ σ := by
      rw [← Real.mul_rpow (by positivity) hn0.le]; ring_nf
    rw [hp, div_le_iff₀ (by positivity)]
    calc ‖a n‖ ≤ K * (n : ℝ) ^ c := hK n hn
      _ ≤ |K| * (n : ℝ) ^ c := by gcongr; exact le_abs_self K
      _ = B * (n : ℝ) ^ (c - σ) * ((2 * π / h) ^ σ * (n : ℝ) ^ σ) := by
          simp only [B]
          rw [Real.rpow_sub hn0]
          have h1 : (h / (2 * π)) ^ σ * (2 * π / h) ^ σ = 1 := by
            rw [← Real.mul_rpow (by positivity) (by positivity)]
            rw [show h / (2 * π) * (2 * π / h) = 1 by field_simp]
            simp
          have h2 : (n : ℝ) ^ σ ≠ 0 := by positivity
          field_simp
          rw [mul_assoc, h1, mul_one]

lemma mellin_phi_sub (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {s : ℂ} (hs : c + 1 < s.re) :
    HasSum (fun i => Gamma s * aa a i / (pp h i : ℂ) ^ s) (mellin (fun t => phi a h t - a 0) s)
    ∧ mellin (fun t => phi a h t - a 0) s = heckeCompletedLSeries a h s := by
  have hp : ∀ i, aa a i = 0 ∨ 0 < pp h i := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · left; simp [aa]
    · right; unfold pp; have : (0:ℝ) < i := by exact_mod_cast hi
      positivity
  have hs0 : 0 < s.re := by linarith
  have hsum := hasSum_mellin (a := aa a) (p := pp h) (F := fun t => phi a h t - a 0) hp hs0
    (fun t ht => hasSum_phi_sub a h hh K A m hK ht) (summable_aa_div a c h hc hh hgrowth hs)
  refine ⟨hsum, ?_⟩
  rw [← hsum.tsum_eq]
  unfold heckeCompletedLSeries LSeries
  rw [← tsum_mul_left]
  congr 1
  funext i
  unfold aa pp LSeries.term
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · simp only [hi.ne', if_false]
    have hi0 : (0:ℝ) < i := by exact_mod_cast hi
    have e1 : ((2 * π * (i : ℝ) / h : ℝ) : ℂ) = ((2 * π / h : ℝ) : ℂ) * ((i : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, Complex.mul_cpow_ofReal_nonneg (by positivity) hi0.le, Complex.cpow_neg]
    have e2 : ((2 * π / h : ℝ) : ℂ) = 2 * (π : ℂ) / (h : ℂ) := by push_cast; ring
    rw [e2]
    have hne1 : (2 * (π : ℂ) / (h : ℂ)) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not
      intro h0
      exfalso
      have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have : 2 * (π : ℂ) / (h : ℂ) ≠ 0 := by
        apply div_ne_zero (mul_ne_zero two_ne_zero ‹_›) ‹_›
      exact this h0
    have hne2 : ((i : ℝ) : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not
      intro h0; exfalso; exact (by exact_mod_cast hi0.ne' : ((i : ℝ) : ℂ) ≠ 0) h0
    push_cast at hne2 ⊢
    field_simp

lemma integral_term_norm (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    IntegrableOn (fun t : ℝ => ‖aa a n‖ * (t ^ (σ - 1) * Real.exp (-(pp h n * t)))) (Ioi 0) ∧
    ∫ t in Ioi 0, ‖aa a n‖ * (t ^ (σ - 1) * Real.exp (-(pp h n * t)))
      = Real.Gamma σ * (‖aa a n‖ / (pp h n) ^ σ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aa]
  · have hp : 0 < pp h n := by
      unfold pp; have : (0:ℝ) < n := by exact_mod_cast hn
      positivity
    have hint : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(pp h n * t))) (Ioi 0) := by
      have := Real.GammaIntegral_convergent hσ
      rw [← mul_zero (pp h n), ← integrableOn_Ioi_comp_mul_left_iff _ _ hp] at this
      refine IntegrableOn.congr_fun (this.const_mul (1 / (pp h n) ^ (σ - 1)))
        (fun t ht => ?_) measurableSet_Ioi
      have ht' : (0:ℝ) < t := ht
      rw [Real.mul_rpow hp.le ht'.le]
      have : (pp h n) ^ (σ - 1) ≠ 0 := by positivity
      field_simp
    refine ⟨hint.const_mul _, ?_⟩
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hp]
    rw [Real.div_rpow zero_le_one hp.le, Real.one_rpow]
    ring

lemma mellinConvergent_phi_sub (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {σ : ℝ} (hσ : c + 1 < σ) :
    MellinConvergent (fun t => phi a h t - a 0) (σ : ℂ) := by
  have hσ0 : 0 < σ := by linarith
  set g : ℕ → ℝ → ℝ := fun n t => ‖aa a n‖ * (t ^ (σ - 1) * Real.exp (-(pp h n * t))) with hg
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0))
      (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1)) (Ioi 0) := by
      intro t ht
      apply ContinuousAt.continuousWithinAt
      exact (continuousAt_cpow_const (b := (σ : ℂ) - 1)
        (Complex.ofReal_mem_slitPlane.2 (ht : (0:ℝ) < t))).comp
          Complex.continuous_ofReal.continuousAt
    have h2 : ContinuousOn (fun t => phi a h t - a 0) (Ioi 0) :=
      (continuousOn_phi a h hh K A m hK).sub continuousOn_const
    exact ContinuousOn.smul (f := fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1))
      (g := fun t => phi a h t - a 0) h1 h2
  refine ⟨hmeas, ?_⟩
  -- finiteness of the lintegral
  have hbound : ∀ t ∈ Ioi (0:ℝ), ‖(t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)‖ₑ ≤
      ∑' n, ENNReal.ofReal (g n t) := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have hs := (hasSum_phi_sub a h hh K A m hK ht').const_smul ((t : ℂ) ^ ((σ : ℂ) - 1))
    rw [← hs.tsum_eq]
    refine le_trans enorm_tsum_le_tsum_enorm (ENNReal.tsum_le_tsum fun n => ?_)
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simp only [hg]
    rw [norm_smul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    rw [show -pp h n * t = -(pp h n * t) by ring]
    nlinarith [norm_nonneg (aa a n), Real.rpow_nonneg ht'.le (σ - 1), Real.exp_pos (-(pp h n * t))]
  have hlin : ∫⁻ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)‖ₑ ≤
      ∑' n, ENNReal.ofReal (Real.Gamma σ * (‖aa a n‖ / (pp h n) ^ σ)) := by
    calc ∫⁻ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)‖ₑ
        ≤ ∫⁻ t in Ioi (0:ℝ), ∑' n, ENNReal.ofReal (g n t) :=
          setLIntegral_mono_ae' measurableSet_Ioi (Filter.Eventually.of_forall hbound)
      _ = ∑' n, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (g n t) := by
          apply lintegral_tsum
          intro n
          apply Measurable.aemeasurable
          apply ENNReal.measurable_ofReal.comp
          simp only [hg]
          fun_prop
      _ = ∑' n, ENNReal.ofReal (Real.Gamma σ * (‖aa a n‖ / (pp h n) ^ σ)) := by
          congr 1
          funext n
          obtain ⟨hi, he⟩ := integral_term_norm a h hh hσ0 n
          rw [← he]
          rw [ofReal_integral_eq_lintegral_ofReal hi]
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht' : (0:ℝ) < t := ht
          simp only [Pi.zero_apply, hg]
          positivity
  have hsum : Summable (fun n => Real.Gamma σ * (‖aa a n‖ / (pp h n) ^ σ)) :=
    (summable_aa_div a c h hc hh hgrowth hσ).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by
      have := Real.Gamma_pos_of_pos hσ0
      have : 0 ≤ ‖aa a n‖ / (pp h n) ^ σ :=
        div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by unfold pp; positivity) _)
      positivity) hsum] at hlin
  exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top

lemma k_le_of_a0_ne (a : ℕ → ℂ) (c h k : ℝ) (C : ℂ) (hc : 0 < c) (hh : 0 < h) (hk : 0 < k)
    (hC : C = 1 ∨ C = -1) (hgrowth : HeckeCoeffGrowth a c) (hA : HeckeAutomorphic a h k C)
    (K A : ℝ) (m : ℕ) (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) (ha0 : a 0 ≠ 0) :
    k ≤ c + 1 := by
  by_contra hlt
  push Not at hlt
  set σ := (c + 1 + k) / 2 with hσdef
  have hσ1 : c + 1 < σ := by linarith
  have hσ2 : σ < k := by linarith
  have hconv := mellinConvergent_phi_sub a c h hc hh hgrowth K A m hK hσ1
  have hCn : ‖C‖ = 1 := by rcases hC with rfl | rfl <;> simp
  obtain ⟨S, hS⟩ := phi_sub_bound a h hh K A m hK
  have ha0p : 0 < ‖a 0‖ := norm_pos_iff.2 ha0
  have hev1 : ∀ᶠ y : ℝ in atTop, S * Real.exp (-(2 * π / h) * (y - 1)) ≤ ‖a 0‖ / 4 := by
    have hβ : 0 < 2 * π / h := by positivity
    have ht : Tendsto (fun y : ℝ => S * Real.exp (-(2 * π / h) * (y - 1))) atTop (𝓝 (S * 0)) := by
      apply Tendsto.const_mul
      apply Real.tendsto_exp_atBot.comp
      apply Tendsto.neg_mul_atTop (by linarith) tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ _ tendsto_id
    rw [mul_zero] at ht
    exact ht.eventually (ge_mem_nhds (by linarith))
  have hev2 : ∀ᶠ y : ℝ in atTop, (4 : ℝ) ≤ y ^ k :=
    (tendsto_rpow_atTop hk).eventually (eventually_ge_atTop 4)
  obtain ⟨Y, hY⟩ := (hev1.and (hev2.and (eventually_ge_atTop (1:ℝ)))).exists_forall_of_atTop
  have hY1 : (1:ℝ) ≤ Y := (hY Y le_rfl).2.2
  set t0 := 1 / Y with ht0def
  have ht0 : 0 < t0 := by positivity
  have hlow : ∀ t ∈ Ioo (0:ℝ) t0,
      ‖a 0‖ / 2 * t ^ (σ - 1 - k) ≤ ‖(t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)‖ := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    set y := 1 / t with hy
    have hy0 : 0 < y := by positivity
    have hyY : Y ≤ y := by
      rw [hy, le_div_iff₀ ht1]
      rw [ht0def, lt_div_iff₀ (by linarith)] at ht2
      linarith
    obtain ⟨hy1, hy2, hy3⟩ := hY y hyY
    have hfe := phi_feq a h k C hA hy0
    have hty : 1 / y = t := by rw [hy]; field_simp
    rw [hty] at hfe
    have hphiy : 3 / 4 * ‖a 0‖ ≤ ‖phi a h y‖ := by
      have := hS y hy3
      have h2 : ‖a 0‖ ≤ ‖phi a h y‖ + ‖phi a h y - a 0‖ := by
        calc ‖a 0‖ = ‖phi a h y - (phi a h y - a 0)‖ := by ring_nf
          _ ≤ ‖phi a h y‖ + ‖phi a h y - a 0‖ := norm_sub_le _ _
      linarith
    have hnorm1 : ‖phi a h t‖ = y ^ k * ‖phi a h y‖ := by
      rw [hfe, norm_smul, norm_mul, hCn, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hy0 k), one_mul]
    have hlow1 : ‖a 0‖ / 2 * y ^ k ≤ ‖phi a h t - a 0‖ := by
      have h3 : ‖phi a h t‖ ≤ ‖phi a h t - a 0‖ + ‖a 0‖ := by
        calc ‖phi a h t‖ = ‖(phi a h t - a 0) + a 0‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [hnorm1] at h3
      nlinarith
    have hyk : y ^ k = t ^ (-k) := by
      rw [hy, Real.rpow_neg ht1.le, one_div, Real.inv_rpow ht1.le]
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht1]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    rw [hyk] at hlow1
    have e : t ^ (σ - 1 - k) = t ^ (σ - 1) * t ^ (-k) := by
      rw [← Real.rpow_add ht1]; ring_nf
    rw [e]
    have := Real.rpow_pos_of_pos ht1 (σ - 1)
    nlinarith
  have hint2 : IntegrableOn (fun t : ℝ => ‖a 0‖ / 2 * t ^ (σ - 1 - k)) (Ioo 0 t0) := by
    have hc' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)) (Ioi 0) :=
      hconv
    refine Integrable.mono' (IntegrableOn.mono_set hc'.norm Ioo_subset_Ioi_self) ?_ ?_
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
      intro t ht
      apply ContinuousAt.continuousWithinAt
      exact (Real.continuousAt_rpow_const _ _ (Or.inl ht.1.ne')).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := ht.1; positivity)]
      exact hlow t ht
  have hint3 : IntegrableOn (fun t : ℝ => t ^ (σ - 1 - k)) (Ioo 0 t0) := by
    have := hint2.const_mul (2 / ‖a 0‖)
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioo
    field_simp
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff ht0).1 hint3
  linarith

lemma mellin_bdd (f : ℝ → ℂ) (hf : ∀ σ : ℝ, MellinConvergent f (σ : ℂ)) (σ₁ σ₂ : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖mellin f s‖ ≤ M := by
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((σ₁ : ℂ) - 1) • f t) (Ioi 0) := hf σ₁
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((σ₂ : ℂ) - 1) • f t) (Ioi 0) := hf σ₂
  have hg := h1.norm.add h2.norm
  refine ⟨∫ t in Ioi (0:ℝ), (‖(t : ℂ) ^ ((σ₁ : ℂ) - 1) • f t‖ + ‖(t : ℂ) ^ ((σ₂ : ℂ) - 1) • f t‖),
    fun s hs1 hs2 => ?_⟩
  unfold mellin
  apply norm_integral_le_of_norm_le hg
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0:ℝ) < t := ht
  simp only [Pi.add_apply]
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.sub_re,
    Complex.ofReal_re, Complex.one_re]
  have hf0 := norm_nonneg (f t)
  have p1 := Real.rpow_nonneg ht'.le (σ₁ - 1)
  have p2 := Real.rpow_nonneg ht'.le (σ₂ - 1)
  rcases le_or_gt t 1 with ht1 | ht1
  · have : t ^ (s.re - 1) ≤ t ^ (σ₁ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht' ht1 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right this hf0, mul_nonneg p2 hf0]
  · have : t ^ (s.re - 1) ≤ t ^ (σ₂ - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right this hf0, mul_nonneg p1 hf0]

end Gelbart

open Complex Real Filter Topology Set MeasureTheory

namespace GelbartJ

/-- boundary integral of a rectangle `[a,b] × [-T,T]` -/
noncomputable def rectI (f : ℂ → ℂ) (a b T : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + (-T) * I)) - (∫ x : ℝ in a..b, f (x + T * I)) +
    I • (∫ y : ℝ in (-T)..T, f (b + y * I)) - I • (∫ y : ℝ in (-T)..T, f (a + y * I))

lemma rectI_eq_zero (f : ℂ → ℂ) (a b T : ℝ) (hf : Differentiable ℂ f) : rectI f a b T = 0 := by
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -T⟩ ⟨b, T⟩
    hf.differentiableOn
  simpa [rectI] using this

lemma log_neg_of_im_neg {w : ℂ} (hw : w.im < 0) : log (-w) = log w + π * I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hw]; push_cast; ring

lemma log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) : log (-w) = log w - π * I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hw]; push_cast; ring

lemma horiz_int (p T a b : ℝ) (hT : T ≠ 0) :
    (∫ x : ℝ in a..b, 1 / ((x : ℂ) + T * I - p)) = log (b - p + T * I) - log (a - p + T * I) := by
  have hne : ∀ x : ℝ, (x : ℂ) + T * I - p ≠ 0 := by
    intro x h; have := congrArg Complex.im h; simp at this; exact hT this
  have hslit : ∀ x : ℝ, (x : ℂ) - p + T * I ∈ slitPlane := by
    intro x; rw [mem_slitPlane_iff]; right; simpa using hT
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => log ((x : ℂ) - p + T * I))]
  · intro x _
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) - p + T * I) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.sub_const (p : ℂ)).add_const (T * I)
    have := h1.clog_real (hslit x)
    rw [show (x : ℂ) + T * I - p = x - p + T * I by ring]
    exact this
  · apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) hne

lemma vert_int_pos (q T : ℝ) (hq : 0 < q) :
    (∫ y : ℝ in (-T)..T, 1 / ((q : ℂ) + y * I)) = -I * (log (q + T * I) - log (q + (-T) * I)) := by
  have hne : ∀ y : ℝ, (q : ℂ) + y * I ≠ 0 := by
    intro y h; have := congrArg Complex.re h; simp at this; linarith
  have hslit : ∀ y : ℝ, (q : ℂ) + y * I ∈ slitPlane := by
    intro y; rw [mem_slitPlane_iff]; left; simpa using hq
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => -I * log ((q : ℂ) + y * I))]
  · push_cast; ring
  · intro y _
    have h1 : HasDerivAt (fun y : ℝ => (q : ℂ) + y * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (q : ℂ)
    have := (h1.clog_real (hslit y)).const_mul (-I)
    have e : (1 / ((q : ℂ) + y * I)) = -I * (I / ((q : ℂ) + y * I)) := by
      rw [← mul_div_assoc, show -I * I = (1:ℂ) by rw [neg_mul, I_mul_I, neg_neg]]
    rw [e]; exact this
  · apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) hne

lemma vert_int_neg (q T : ℝ) (hq : q < 0) :
    (∫ y : ℝ in (-T)..T, 1 / ((q : ℂ) + y * I)) =
      -I * (log (-q + (-T) * I) - log (-q + T * I)) := by
  have hne : ∀ y : ℝ, (q : ℂ) + y * I ≠ 0 := by
    intro y h; have := congrArg Complex.re h; simp at this; linarith
  have hslit : ∀ y : ℝ, -(q : ℂ) + (-y) * I ∈ slitPlane := by
    intro y; rw [mem_slitPlane_iff]; left; simpa using hq
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => -I * log (-(q : ℂ) + (-y) * I))]
  · push_cast; ring
  · intro y _
    have h1 : HasDerivAt (fun y : ℝ => -(q : ℂ) + (-(y : ℂ)) * I) (-I) y := by
      simpa using (((hasDerivAt_id y).ofReal_comp.neg).mul_const I).const_add (-(q : ℂ))
    have := (h1.clog_real (by simpa using hslit y)).const_mul (-I)
    have e : (1 / ((q : ℂ) + y * I)) = -I * (-I / (-(q : ℂ) + -(y : ℂ) * I)) := by
      rw [← mul_div_assoc, show -I * -I = (-1:ℂ) by rw [neg_mul_neg, I_mul_I],
        show -(q : ℂ) + -(y : ℂ) * I = -((q : ℂ) + y * I) by ring, div_neg, neg_div, neg_neg]
    rw [e]; exact this
  · apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) hne

lemma rectI_inv (p a b T : ℝ) (hap : a < p) (hpb : p < b) (hT : 0 < T) :
    rectI (fun s => 1 / (s - p)) a b T = 2 * π * I := by
  unfold rectI
  have e1 := horiz_int p (-T) a b (by linarith)
  have e2 := horiz_int p T a b (by linarith)
  have e3 := vert_int_pos (b - p) T (by linarith)
  have e4 := vert_int_neg (a - p) T (by linarith)
  have r3 : (∫ y : ℝ in (-T)..T, 1 / ((b : ℂ) + y * I - p)) =
      ∫ y : ℝ in (-T)..T, 1 / (((b - p : ℝ) : ℂ) + y * I) := by
    congr 1; funext y; push_cast; ring_nf
  have r4 : (∫ y : ℝ in (-T)..T, 1 / ((a : ℂ) + y * I - p)) =
      ∫ y : ℝ in (-T)..T, 1 / (((a - p : ℝ) : ℂ) + y * I) := by
    congr 1; funext y; push_cast; ring_nf
  simp only [smul_eq_mul]
  rw [r3, r4, e3, e4]
  push_cast at e1 e2 ⊢
  rw [e1, e2]
  have n1 : log ((a : ℂ) - p + T * I) = log (-((p : ℂ) - a + (-T) * I)) := by ring_nf
  have n2 : log ((a : ℂ) - p + (-T : ℝ) * I) = log (-((p : ℂ) - a + T * I)) := by
    push_cast; ring_nf
  push_cast at n2
  rw [n1, n2, log_neg_of_im_neg (w := (p : ℂ) - a + -T * I) (by simp; linarith),
    log_neg_of_im_pos (w := (p : ℂ) - a + T * I) (by simp; linarith)]
  have h4 : -((a : ℂ) - p) = p - a := by ring
  rw [h4]
  ring_nf
  rw [I_sq]; ring

end GelbartJ

open Complex Real Filter Topology Set MeasureTheory

namespace GelbartJ

lemma rectI_pole (h : ℂ → ℂ) (hh : Differentiable ℂ h) (p a b T : ℝ) (hap : a < p) (hpb : p < b)
    (hT : 0 < T) : rectI (fun s => h s / (s - p)) a b T = 2 * π * I * h p := by
  have hd : Differentiable ℂ (dslope h p) := by
    intro z
    have := (Complex.differentiableOn_dslope (f := h) (s := univ) (c := (p : ℂ))
      Filter.univ_mem).2 hh.differentiableOn
    exact this.differentiableAt Filter.univ_mem
  have hdc : Continuous (dslope h p) := hd.continuous
  have key : ∀ s : ℂ, s ≠ p → h s / (s - p) = dslope h p s + h p * (1 / (s - p)) := by
    intro s hs
    rw [dslope_of_ne _ hs, slope_def_field]
    have : s - p ≠ 0 := sub_ne_zero.2 hs
    field_simp
    ring
  have z0 := rectI_eq_zero (dslope h p) a b T hd
  have z1 := rectI_inv p a b T hap hpb hT
  -- edges avoid p
  have nb : ∀ x : ℝ, (x : ℂ) + (-(T : ℂ)) * I ≠ p := by
    intro x e; have := congrArg Complex.im e; simp at this; linarith
  have nt : ∀ x : ℝ, (x : ℂ) + (T : ℝ) * I ≠ p := by
    intro x e; have := congrArg Complex.im e; simp at this; linarith
  have nr : ∀ y : ℝ, (b : ℂ) + y * I ≠ p := by
    intro y e; have := congrArg Complex.re e; simp at this; linarith
  have nl : ∀ y : ℝ, (a : ℂ) + y * I ≠ p := by
    intro y e; have := congrArg Complex.re e; simp at this; linarith
  have ci : ∀ (u : ℝ → ℂ), Continuous u → (∀ t, u t ≠ p) →
      IntervalIntegrable (fun t => 1 / (u t - p)) volume (-T) T ∧
      ∀ c d : ℝ, IntervalIntegrable (fun t => 1 / (u t - p)) volume c d := by
    intro u hu hne
    have : Continuous (fun t => 1 / (u t - p)) :=
      continuous_const.div (hu.sub continuous_const) (fun t => sub_ne_zero.2 (hne t))
    exact ⟨this.intervalIntegrable _ _, fun c d => this.intervalIntegrable _ _⟩
  have cd : ∀ (u : ℝ → ℂ), Continuous u → ∀ c d : ℝ,
      IntervalIntegrable (fun t => dslope h p (u t)) volume c d :=
    fun u hu c d => (hdc.comp hu).intervalIntegrable _ _
  have split : ∀ (u : ℝ → ℂ), Continuous u → (∀ t, u t ≠ p) → ∀ c d : ℝ,
      (∫ t in c..d, h (u t) / (u t - p)) =
        (∫ t in c..d, dslope h p (u t)) + h p * ∫ t in c..d, 1 / (u t - p) := by
    intro u hu hne c d
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (cd u hu c d)
      (((ci u hu hne).2 c d).const_mul _)]
    congr 1; funext t; exact key _ (hne t)
  unfold rectI at z0 z1 ⊢
  simp only [smul_eq_mul] at z0 z1 ⊢
  rw [split (fun x : ℝ => (x : ℂ) + (-(T : ℂ)) * I) (by fun_prop) nb,
    split (fun x : ℝ => (x : ℂ) + (T : ℝ) * I) (by fun_prop) nt,
    split (fun y : ℝ => (b : ℂ) + y * I) (by fun_prop) nr,
    split (fun y : ℝ => (a : ℂ) + y * I) (by fun_prop) nl]
  linear_combination z0 + h p * z1

lemma line_diff (f : ℂ → ℂ) (a b : ℝ) (L : ℂ) (hrect : ∀ᶠ T : ℝ in atTop, rectI f a b T = L)
    (ha : Integrable (fun y : ℝ => f (a + y * I))) (hb : Integrable (fun y : ℝ => f (b + y * I)))
    (B : ℝ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (hbd : ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, x ∈ uIcc a b →
      ‖f (x + T * I)‖ ≤ B T ∧ ‖f (x + (-T) * I)‖ ≤ B T) :
    I * (∫ y : ℝ, f (b + y * I)) - I * (∫ y : ℝ, f (a + y * I)) = L := by
  have hlim : Tendsto (fun T => rectI f a b T) atTop
      (𝓝 (0 - 0 + I * (∫ y : ℝ, f (b + y * I)) - I * (∫ y : ℝ, f (a + y * I)))) := by
    unfold rectI
    simp only [smul_eq_mul]
    have hneg : Tendsto (fun T : ℝ => -T) atTop atBot := tendsto_neg_atTop_atBot
    have hv1 := intervalIntegral_tendsto_integral hb hneg tendsto_id
    have hv2 := intervalIntegral_tendsto_integral ha hneg tendsto_id
    have hsmall : ∀ (s : ℝ), (s = 1 ∨ s = -1) →
        Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f (x + (s * T : ℝ) * I)) atTop (𝓝 0) := by
      intro s hs
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (by simpa using hB.mul_const |b - a|)
      · filter_upwards [hbd] with T hT
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
        have hx' : x ∈ uIcc a b := Ioc_subset_Icc_self (by simpa [uIoc] using hx)
        rcases hs with rfl | rfl
        · simpa using (hT x hx').1
        · simpa using (hT x hx').2
    have hs1 := hsmall 1 (Or.inl rfl)
    have hs2 := hsmall (-1) (Or.inr rfl)
    simp only [one_mul, neg_one_mul] at hs1 hs2
    push_cast at hs2
    simp only [id] at hv1 hv2
    exact ((hs2.sub hs1).add (hv1.const_mul I)).sub (hv2.const_mul I)
  have := tendsto_nhds_unique (hlim.congr' hrect) tendsto_const_nhds
  rw [← this]; ring

end GelbartJ

open Complex Real Filter Topology Set MeasureTheory Asymptotics

namespace Gelbart

lemma norm_Gamma_le_re {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx' : (0:ℝ) < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx']
  simp

lemma norm_Gamma_mul_sq_le {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ * ‖s‖ ^ 2 ≤ Real.Gamma (s.re + 2) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have e : Complex.Gamma (s + 2) = (s + 1) * (s * Complex.Gamma s) := by
    rw [show s + 2 = (s + 1) + 1 by ring, Complex.Gamma_add_one _ hs1,
      Complex.Gamma_add_one _ hs0]
  have h2 : 0 < (s + 2).re := by simp; linarith
  have hb := norm_Gamma_le_re h2
  rw [e] at hb
  simp only [Complex.add_re, show (2:ℂ).re = 2 by norm_num] at hb
  rw [norm_mul, norm_mul] at hb
  have hle : ‖s‖ ≤ ‖s + 1‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    simp [Complex.normSq_apply]; nlinarith
  have := norm_nonneg (Complex.Gamma s)
  have := norm_nonneg s
  nlinarith [mul_le_mul_of_nonneg_right hle (mul_nonneg (norm_nonneg s) (norm_nonneg (Complex.Gamma s)))]

lemma Phi_line_bound (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) {σ : ℝ} (hσ : c + 1 < σ) :
    ∃ K : ℝ, ∀ y : ℝ, ‖heckeCompletedLSeries a h (σ + y * I)‖ ≤ K * (1 + y ^ 2)⁻¹ := by
  obtain ⟨K0, _, m, hK⟩ := coeff_bound a c hc hgrowth
  have hσ0 : 0 < σ := by linarith
  set S := ∑' i, ‖aa a i‖ / (pp h i) ^ σ with hS
  have hsum := summable_aa_div a c h hc hh hgrowth hσ
  have hS0 : 0 ≤ S := tsum_nonneg (fun i => div_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (by unfold pp; positivity) _))
  set μ := min 1 (σ ^ 2) with hμ
  have hμ0 : 0 < μ := lt_min one_pos (by positivity)
  refine ⟨S * Real.Gamma (σ + 2) / μ, fun y => ?_⟩
  set s : ℂ := σ + y * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs : c + 1 < s.re := by rw [hsre]; exact hσ
  obtain ⟨hsum2, hmel⟩ := mellin_phi_sub a c h hc hh hgrowth K0 (‖a 0‖) m hK hs
  rw [← hmel]
  have hbound : ‖mellin (fun t => phi a h t - a 0) s‖ ≤ ‖Complex.Gamma s‖ * S := by
    rw [← tsum_mul_left, ← hsum2.tsum_eq]
    refine tsum_of_norm_bounded (f := fun i => Complex.Gamma s * aa a i / (pp h i : ℂ) ^ s)
      (hsum.mul_left ‖Complex.Gamma s‖).hasSum (fun i => ?_)
    · show ‖Complex.Gamma s * aa a i / (pp h i : ℂ) ^ s‖ ≤ ‖Complex.Gamma s‖ * (‖aa a i‖ / (pp h i) ^ σ)
      rw [mul_div_assoc, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [aa]
      · have hp : 0 < pp h i := by
          unfold pp; have : (0:ℝ) < i := by exact_mod_cast hi
          positivity
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hp, hsre]
  refine hbound.trans ?_
  have hG := norm_Gamma_mul_sq_le (s := s) (by rw [hsre]; exact hσ0)
  rw [hsre] at hG
  have hn : ‖s‖ ^ 2 = σ ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [hsdef]; ring
  rw [hn] at hG
  have hμle : μ * (1 + y ^ 2) ≤ σ ^ 2 + y ^ 2 := by
    have h1 : μ ≤ 1 := min_le_left _ _
    have h2 : μ ≤ σ ^ 2 := min_le_right _ _
    nlinarith [sq_nonneg y]
  have hpos : 0 < 1 + y ^ 2 := by positivity
  have hq : 0 < σ ^ 2 + y ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ0]
  have hGn : ‖Complex.Gamma s‖ ≤ Real.Gamma (σ + 2) / (σ ^ 2 + y ^ 2) := by
    rw [le_div_iff₀ hq]; exact hG
  calc ‖Complex.Gamma s‖ * S * μ
      ≤ Real.Gamma (σ + 2) / (σ ^ 2 + y ^ 2) * S * μ := by gcongr
    _ ≤ S * Real.Gamma (σ + 2) * (1 + y ^ 2)⁻¹ := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hq]
      have hGp : 0 ≤ Real.Gamma (σ + 2) := (Real.Gamma_pos_of_pos (by linarith)).le
      have : S * Real.Gamma (σ + 2) * (1 + y ^ 2)⁻¹ * (σ ^ 2 + y ^ 2) ≥
          S * Real.Gamma (σ + 2) * (1 + y ^ 2)⁻¹ * (μ * (1 + y ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hμle; positivity
      have e : S * Real.Gamma (σ + 2) * (1 + y ^ 2)⁻¹ * (μ * (1 + y ^ 2)) =
          Real.Gamma (σ + 2) * S * μ := by field_simp
      linarith

end Gelbart

open Complex Real Filter Topology Set MeasureTheory

namespace GelbartJ

/-- `Z` is a set of real points not on the vertical edges -/
def Avoid (Z : Set ℂ) (a b : ℝ) : Prop := ∀ z ∈ Z, z.im = 0 ∧ z.re ≠ a ∧ z.re ≠ b

lemma edge_ne {Z : Set ℂ} {a b T : ℝ} (hZ : Avoid Z a b) (hT : T ≠ 0) :
    (∀ x : ℝ, (x : ℂ) + (-(T : ℂ)) * I ∉ Z) ∧ (∀ x : ℝ, (x : ℂ) + (T : ℂ) * I ∉ Z) ∧
    (∀ y : ℝ, (b : ℂ) + y * I ∉ Z) ∧ (∀ y : ℝ, (a : ℂ) + y * I ∉ Z) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have := (hZ _ hx).1; simp at this; exact hT this
  · have := (hZ _ hx).1; simp at this; exact hT this
  · have := (hZ _ hy).2.2; simp at this
  · have := (hZ _ hy).2.1; simp at this

lemma rectI_congr (f g : ℂ → ℂ) {Z : Set ℂ} {a b T : ℝ} (hZ : Avoid Z a b) (hT : T ≠ 0)
    (hfg : ∀ s, s ∉ Z → f s = g s) : rectI f a b T = rectI g a b T := by
  obtain ⟨h1, h2, h3, h4⟩ := edge_ne hZ hT
  unfold rectI
  have e1 : (fun x : ℝ => f (x + (-(T : ℂ)) * I)) = fun x : ℝ => g (x + (-(T : ℂ)) * I) :=
    funext fun x => hfg _ (h1 x)
  have e2 : (fun x : ℝ => f (x + (T : ℂ) * I)) = fun x : ℝ => g (x + (T : ℂ) * I) :=
    funext fun x => hfg _ (h2 x)
  have e3 : (fun y : ℝ => f (b + y * I)) = fun y : ℝ => g (b + y * I) :=
    funext fun y => hfg _ (h3 y)
  have e4 : (fun y : ℝ => f (a + y * I)) = fun y : ℝ => g (a + y * I) :=
    funext fun y => hfg _ (h4 y)
  simp only [e1, e2, e3, e4]

lemma edge_ii (f : ℂ → ℂ) {Z : Set ℂ} {a b T : ℝ} (hZ : Avoid Z a b) (hT : T ≠ 0)
    (hf : ∀ s, s ∉ Z → ContinuousAt f s) :
    IntervalIntegrable (fun x : ℝ => f (x + (-(T : ℂ)) * I)) volume a b ∧
    IntervalIntegrable (fun x : ℝ => f (x + (T : ℂ) * I)) volume a b ∧
    IntervalIntegrable (fun y : ℝ => f (b + y * I)) volume (-T) T ∧
    IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume (-T) T := by
  obtain ⟨h1, h2, h3, h4⟩ := edge_ne hZ hT
  refine ⟨Continuous.intervalIntegrable ?_ _ _, Continuous.intervalIntegrable ?_ _ _,
    Continuous.intervalIntegrable ?_ _ _, Continuous.intervalIntegrable ?_ _ _⟩
  · exact continuous_iff_continuousAt.2 fun x => ContinuousAt.comp (g := f) (f := fun x : ℝ => (x : ℂ) + (-(T : ℂ)) * I) (hf _ (h1 x)) (by fun_prop)
  · exact continuous_iff_continuousAt.2 fun x => ContinuousAt.comp (g := f) (f := fun x : ℝ => (x : ℂ) + (T : ℂ) * I) (hf _ (h2 x)) (by fun_prop)
  · exact continuous_iff_continuousAt.2 fun x => ContinuousAt.comp (g := f) (f := fun y : ℝ => (b : ℂ) + y * I) (hf _ (h3 x)) (by fun_prop)
  · exact continuous_iff_continuousAt.2 fun x => ContinuousAt.comp (g := f) (f := fun y : ℝ => (a : ℂ) + y * I) (hf _ (h4 x)) (by fun_prop)

lemma rectI_lin (f g : ℂ → ℂ) (c : ℂ) {Z : Set ℂ} {a b T : ℝ} (hZ : Avoid Z a b) (hT : T ≠ 0)
    (hf : ∀ s, s ∉ Z → ContinuousAt f s) (hg : ∀ s, s ∉ Z → ContinuousAt g s) :
    rectI (fun s => f s + c * g s) a b T = rectI f a b T + c * rectI g a b T := by
  obtain ⟨f1, f2, f3, f4⟩ := edge_ii f hZ hT hf
  obtain ⟨g1, g2, g3, g4⟩ := edge_ii g hZ hT hg
  unfold rectI
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_add f1 (g1.const_mul c), intervalIntegral.integral_add f2 (g2.const_mul c),
    intervalIntegral.integral_add f3 (g3.const_mul c), intervalIntegral.integral_add f4 (g4.const_mul c)]
  simp only [intervalIntegral.integral_const_mul]
  ring

end GelbartJ

open Complex Real Filter Topology Set MeasureTheory

namespace Gelbart
open GelbartJ

noncomputable def Hf (k x ε : ℝ) (s : ℂ) : ℂ := cexp (ε * (s - k / 2) ^ 2) * (x : ℂ) ^ (-s)

lemma Hf_diff (k x ε : ℝ) (hx : 0 < x) : Differentiable ℂ (Hf k x ε) := by
  unfold Hf
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  exact (by fun_prop : Differentiable ℂ fun s : ℂ => cexp (ε * (s - k / 2) ^ 2)).mul
    (Differentiable.const_cpow (by fun_prop) (Or.inl hx0))

lemma norm_Hf (k x ε : ℝ) (hx : 0 < x) (s : ℂ) :
    ‖Hf k x ε s‖ = Real.exp (ε * ((s.re - k / 2) ^ 2 - s.im ^ 2)) * x ^ (-s.re) := by
  unfold Hf
  rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 2
  simp [sq, Complex.mul_re]

lemma norm_Hf_le (k x ε : ℝ) (hx : 0 < x) (hε : 0 ≤ ε) (s : ℂ) :
    ‖Hf k x ε s‖ ≤ Real.exp (ε * (s.re - k / 2) ^ 2) * x ^ (-s.re) := by
  rw [norm_Hf k x ε hx]
  gcongr
  nlinarith [sq_nonneg s.im]

noncomputable def Psi (F : ℂ → ℂ) (k : ℝ) (C a0 : ℂ) (s : ℂ) : ℂ :=
  F s - a0 / s - C * a0 / (k - s)

lemma Psi_contAt (F : ℂ → ℂ) (hF : Differentiable ℂ F) (k : ℝ) (C a0 : ℂ) (s : ℂ)
    (hs0 : s ≠ 0) (hsk : s ≠ k) : ContinuousAt (Psi F k C a0) s := by
  unfold Psi
  exact (hF.continuous.continuousAt.sub (continuousAt_const.div continuousAt_id hs0)).sub
    (continuousAt_const.div (continuousAt_const.sub continuousAt_id) (sub_ne_zero.2 (Ne.symm hsk)))

lemma Psi_fe (F : ℂ → ℂ) (k : ℝ) (C a0 : ℂ) (hC : C * C = 1)
    (hFE : ∀ s, F (k - s) = C * F s) (s : ℂ) :
    Psi F k C a0 (k - s) = C * Psi F k C a0 s := by
  unfold Psi
  rw [hFE, show (k : ℂ) - (k - s) = s by ring]
  have : C * (C * a0 / (k - s)) = a0 / (k - s) := by
    rw [mul_div_assoc', ← mul_assoc, hC, one_mul]
  rw [mul_sub, mul_sub, this]
  ring

lemma rect_value (F : ℂ → ℂ) (hF : Differentiable ℂ F) (k : ℝ) (hk : 0 < k) (C a0 : ℂ)
    (σ : ℝ) (hσ : k < σ) (x : ℝ) (hx : 0 < x) (ε : ℝ) (T : ℝ) (hT : 0 < T) :
    rectI (fun s => Psi F k C a0 s * Hf k x ε s) (k - σ) σ T =
      2 * π * I * (-a0 * Hf k x ε 0 + C * a0 * Hf k x ε k) := by
  set Z : Set ℂ := {0, (k : ℂ)} with hZdef
  have hZ : Avoid Z (k - σ) σ := by
    intro z hz
    rcases hz with rfl | hz
    · simp; constructor <;> linarith
    · rw [mem_singleton_iff] at hz; subst hz; simp; constructor <;> linarith
  have hT0 : T ≠ 0 := hT.ne'
  have hH := Hf_diff k x ε hx
  have hnZ : ∀ s, s ∉ Z → s ≠ 0 ∧ s ≠ (k : ℂ) := by
    intro s hs; simp [hZdef, not_or] at hs; exact hs
  have e1 : rectI (fun s => Psi F k C a0 s * Hf k x ε s) (k - σ) σ T =
      rectI (fun s => (F s * Hf k x ε s + (-a0) * (Hf k x ε s / (s - ((0:ℝ) : ℂ)))) +
        (C * a0) * (Hf k x ε s / (s - (k : ℂ)))) (k - σ) σ T := by
    apply rectI_congr _ _ hZ hT0
    intro s hs
    obtain ⟨h0, hk'⟩ := hnZ s hs
    have h1 : (k : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hk')
    have h2 : s - (k : ℂ) ≠ 0 := sub_ne_zero.2 hk'
    unfold Psi
    push_cast
    field_simp
    ring
  have cH : ∀ p : ℂ, ∀ s, s ≠ p → ContinuousAt (fun s => Hf k x ε s / (s - p)) s := by
    intro p s hs
    exact hH.continuous.continuousAt.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hs)
  have cFH : ∀ s, s ∉ Z → ContinuousAt (fun s => F s * Hf k x ε s) s :=
    fun s _ => (hF.mul hH).continuous.continuousAt
  have c0 : ∀ s, s ∉ Z → ContinuousAt (fun s => Hf k x ε s / (s - ((0:ℝ) : ℂ))) s := by
    intro s hs; exact cH _ s (by simpa using (hnZ s hs).1)
  have ck : ∀ s, s ∉ Z → ContinuousAt (fun s => Hf k x ε s / (s - (k : ℂ))) s := by
    intro s hs; exact cH _ s (hnZ s hs).2
  have c1 : ∀ s, s ∉ Z → ContinuousAt
      (fun s => F s * Hf k x ε s + (-a0) * (Hf k x ε s / (s - ((0:ℝ) : ℂ)))) s := by
    intro s hs; exact (cFH s hs).add ((c0 s hs).const_mul _)
  rw [e1, rectI_lin _ _ _ hZ hT0 c1 ck, rectI_lin _ _ _ hZ hT0 cFH c0,
    rectI_eq_zero (fun s => F s * Hf k x ε s) _ _ _ (hF.mul hH),
    rectI_pole _ hH 0 _ _ _ (by linarith) (by linarith) hT,
    rectI_pole _ hH k _ _ _ (by linarith) (by linarith) hT]
  push_cast; ring

end Gelbart

open Complex Real Filter Topology Set MeasureTheory

namespace Gelbart
open GelbartJ

lemma rpow_neg_le_sum (x : ℝ) (hx : 0 < x) {u v t : ℝ} (hut : u ≤ t) (htv : t ≤ v) :
    x ^ (-t) ≤ x ^ (-u) + x ^ (-v) := by
  rcases le_or_gt 1 x with h1 | h1
  · have : x ^ (-t) ≤ x ^ (-u) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    have := Real.rpow_nonneg hx.le (-v); linarith
  · have : x ^ (-t) ≤ x ^ (-v) := Real.rpow_le_rpow_of_exponent_ge hx h1.le (by linarith)
    have := Real.rpow_nonneg hx.le (-u); linarith

lemma Psi_strip_bound (F : ℂ → ℂ) (k : ℝ) (C a0 : ℂ) (σ M : ℝ)
    (hM : ∀ s : ℂ, k - σ ≤ s.re → s.re ≤ σ → ‖F s‖ ≤ M) (s : ℂ) (h1 : k - σ ≤ s.re)
    (h2 : s.re ≤ σ) (him : 1 ≤ |s.im|) : ‖Psi F k C a0 s‖ ≤ M + ‖a0‖ + ‖C * a0‖ := by
  unfold Psi
  have hs : 1 ≤ ‖s‖ := him.trans (Complex.abs_im_le_norm s)
  have hks : 1 ≤ ‖(k : ℂ) - s‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simpa [abs_neg] using him
  have e1 : ‖a0 / s‖ ≤ ‖a0‖ := by rw [norm_div]; exact div_le_self (norm_nonneg _) hs
  have e2 : ‖C * a0 / (k - s)‖ ≤ ‖C * a0‖ := by
    rw [norm_div]; exact div_le_self (norm_nonneg _) hks
  calc ‖F s - a0 / s - C * a0 / (k - s)‖ ≤ ‖F s‖ + ‖a0 / s‖ + ‖C * a0 / (k - s)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ M + ‖a0‖ + ‖C * a0‖ := by gcongr; exact hM s h1 h2

lemma eps_identity (F : ℂ → ℂ) (hF : Differentiable ℂ F) (k : ℝ) (hk : 0 < k) (C a0 : ℂ)
    (hC : C * C = 1) (hFE : ∀ s, F (k - s) = C * F s)
    (σ : ℝ) (hσ : k < σ) (M : ℝ) (hM : ∀ s : ℂ, k - σ ≤ s.re → s.re ≤ σ → ‖F s‖ ≤ M)
    (K : ℝ) (hK : ∀ y : ℝ, ‖Psi F k C a0 (σ + y * I)‖ ≤ K * (1 + y ^ 2)⁻¹)
    (x : ℝ) (hx : 0 < x) (ε : ℝ) (hε : 0 < ε) :
    I * (∫ y : ℝ, Psi F k C a0 (σ + y * I) * Hf k x ε (σ + y * I)) -
      I * (∫ y : ℝ, Psi F k C a0 ((k - σ : ℝ) + y * I) * Hf k x ε ((k - σ : ℝ) + y * I)) =
      2 * π * I * (-a0 * Hf k x ε 0 + C * a0 * Hf k x ε k) := by
  set R := σ - k / 2 with hR
  set X := x ^ (-σ) + x ^ (-(k - σ)) with hXdef
  have hX : 0 ≤ X := by
    have := Real.rpow_nonneg hx.le (-σ); have := Real.rpow_nonneg hx.le (-(k - σ)); linarith
  have hC1 : ‖C‖ = 1 := by
    have : ‖C‖ * ‖C‖ = 1 := by rw [← norm_mul, hC, norm_one]
    nlinarith [norm_nonneg C]
  have hHb : ∀ s : ℂ, k - σ ≤ s.re → s.re ≤ σ →
      ‖Hf k x ε s‖ ≤ Real.exp (ε * (R ^ 2 - s.im ^ 2)) * X := by
    intro s h1 h2
    rw [norm_Hf k x ε hx]
    apply mul_le_mul (Real.exp_le_exp.2 ?_) ?_ (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
    · have : (s.re - k / 2) ^ 2 ≤ R ^ 2 := by nlinarith
      apply mul_le_mul_of_nonneg_left _ hε.le
      linarith
    · have := rpow_neg_le_sum x hx h1 h2
      rw [hXdef]; linarith
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans (hK 0); simpa using this
  have hcont : ∀ t : ℝ, (t ≠ 0) → (t ≠ k) →
      Continuous (fun y : ℝ => Psi F k C a0 (t + y * I) * Hf k x ε (t + y * I)) := by
    intro t ht0 htk
    apply Continuous.mul
    · refine continuous_iff_continuousAt.2 fun y => ?_
      refine ContinuousAt.comp (g := Psi F k C a0) (f := fun y : ℝ => (t : ℂ) + y * I) ?_
        (by fun_prop)
      apply Psi_contAt F hF
      · intro h; have := congrArg Complex.re h; simp at this; exact ht0 this
      · intro h; have := congrArg Complex.re h; simp at this; exact htk this
    · exact (Hf_diff k x ε hx).continuous.comp (by fun_prop)
  have hb : Integrable (fun y : ℝ => Psi F k C a0 (σ + y * I) * Hf k x ε (σ + y * I)) := by
    refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul K).mul_const
      (Real.exp (ε * R ^ 2) * X)) (hcont σ (by linarith) hσ.ne').aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    have h1 := hHb (σ + y * I) (by simp; linarith) (by simp)
    have h2 : Real.exp (ε * (R ^ 2 - (σ + y * I : ℂ).im ^ 2)) ≤ Real.exp (ε * R ^ 2) := by
      gcongr; nlinarith [sq_nonneg (σ + y * I : ℂ).im]
    have h3 := hK y
    calc ‖Psi F k C a0 (σ + y * I)‖ * ‖Hf k x ε (σ + y * I)‖
        ≤ (K * (1 + y ^ 2)⁻¹) * (Real.exp (ε * R ^ 2) * X) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = _ := by ring
  have hlineA : ∀ y : ℝ, Psi F k C a0 ((k - σ : ℝ) + y * I) = C * Psi F k C a0 (σ + (-y : ℝ) * I) := by
    intro y
    rw [← Psi_fe F k C a0 hC hFE]
    congr 1; push_cast; ring
  have ha : Integrable (fun y : ℝ =>
      Psi F k C a0 ((k - σ : ℝ) + y * I) * Hf k x ε ((k - σ : ℝ) + y * I)) := by
    refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul K).mul_const
      (Real.exp (ε * R ^ 2) * X)) (hcont (k - σ) (by linarith) (by linarith)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, hlineA, norm_mul, hC1, one_mul]
    have h1 := hHb ((k - σ : ℝ) + y * I) (by simp) (by simp; linarith)
    have h2 : Real.exp (ε * (R ^ 2 - (((k - σ : ℝ) : ℂ) + y * I).im ^ 2)) ≤ Real.exp (ε * R ^ 2) := by
      gcongr; nlinarith [sq_nonneg (((k - σ : ℝ) : ℂ) + y * I).im]
    have h3 := hK (-y)
    rw [neg_sq] at h3
    calc ‖Psi F k C a0 (σ + (-y : ℝ) * I)‖ * ‖Hf k x ε ((k - σ : ℝ) + y * I)‖
        ≤ (K * (1 + y ^ 2)⁻¹) * (Real.exp (ε * R ^ 2) * X) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = _ := by ring
  -- horizontal bound
  set B : ℝ → ℝ := fun T => (M + ‖a0‖ + ‖C * a0‖) * (Real.exp (ε * (R ^ 2 - T ^ 2)) * X) with hBdef
  have hBt : Tendsto B atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => T ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    have h2 : Tendsto (fun T : ℝ => ε * (R ^ 2 - T ^ 2)) atTop atBot := by
      have := tendsto_atBot_add_const_left atTop (ε * R ^ 2)
        (tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hε))
      refine this.congr (fun T => ?_)
      simp; ring
    have h3 := (Real.tendsto_exp_atBot.comp h2).mul_const X
    have h4 := h3.const_mul (M + ‖a0‖ + ‖C * a0‖)
    simp only [zero_mul, mul_zero] at h4
    exact h4
  have hbd : ∀ᶠ T : ℝ in atTop, ∀ x' : ℝ, x' ∈ uIcc (k - σ) σ →
      ‖(fun s => Psi F k C a0 s * Hf k x ε s) (x' + T * I)‖ ≤ B T ∧
      ‖(fun s => Psi F k C a0 s * Hf k x ε s) (x' + (-T) * I)‖ ≤ B T := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    intro x' hx'
    rw [uIcc_of_le (by linarith)] at hx'
    obtain ⟨hx1, hx2⟩ := hx'
    have hM0 : 0 ≤ M + ‖a0‖ + ‖C * a0‖ :=
      (norm_nonneg _).trans (Psi_strip_bound F k C a0 σ M hM (x' + T * I) (by simp [hx1])
        (by simp [hx2]) (by simp; rw [abs_of_pos (by linarith)]; exact hT))
    constructor
    · simp only [norm_mul]
      have p1 := Psi_strip_bound F k C a0 σ M hM (x' + T * I) (by simp [hx1]) (by simp [hx2])
        (by simp; rw [abs_of_pos (by linarith)]; exact hT)
      have p2 := hHb (x' + T * I) (by simp [hx1]) (by simp [hx2])
      rw [show ((x' : ℂ) + T * I).im = T by simp] at p2
      exact mul_le_mul p1 p2 (norm_nonneg _) hM0
    · simp only [norm_mul]
      have p1 := Psi_strip_bound F k C a0 σ M hM (x' + (-T) * I) (by simp [hx1]) (by simp [hx2])
        (by simp; rw [abs_of_pos (by linarith)]; exact hT)
      have p2 := hHb (x' + (-T) * I) (by simp [hx1]) (by simp [hx2])
      rw [show ((x' : ℂ) + (-T) * I).im = -T by simp, neg_sq] at p2
      exact mul_le_mul p1 p2 (norm_nonneg _) hM0
  have hrect : ∀ᶠ T : ℝ in atTop, rectI (fun s => Psi F k C a0 s * Hf k x ε s) (k - σ) σ T =
      2 * π * I * (-a0 * Hf k x ε 0 + C * a0 * Hf k x ε k) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact rect_value F hF k hk C a0 σ hσ x hx ε T hT
  exact line_diff (fun s => Psi F k C a0 s * Hf k x ε s) (k - σ) σ _ hrect ha hb B hBt hbd

end Gelbart

open Complex Real Filter Topology Set MeasureTheory

namespace Gelbart
open GelbartJ

lemma Hf_unif (k x ε σ : ℝ) (hx : 0 < x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (s : ℂ)
    (h1 : k - σ ≤ s.re) (h2 : s.re ≤ σ) :
    ‖Hf k x ε s‖ ≤ Real.exp ((σ - k / 2) ^ 2) * (x ^ (-σ) + x ^ (-(k - σ))) := by
  rw [norm_Hf k x ε hx]
  apply mul_le_mul (Real.exp_le_exp.2 ?_) ?_ (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  · have e1 : (s.re - k / 2) ^ 2 ≤ (σ - k / 2) ^ 2 := by nlinarith
    have e2 : (s.re - k / 2) ^ 2 - s.im ^ 2 ≤ (σ - k / 2) ^ 2 := by nlinarith [sq_nonneg s.im]
    have e3 : 0 ≤ (σ - k / 2) ^ 2 := sq_nonneg _
    rcases le_or_gt 0 ((s.re - k / 2) ^ 2 - s.im ^ 2) with h | h
    · nlinarith
    · nlinarith
  · have := rpow_neg_le_sum x hx h1 h2; linarith

lemma Hf_tendsto (k x : ℝ) (s : ℂ) :
    Tendsto (fun n : ℕ => Hf k x (1 / ((n : ℝ) + 1)) s) atTop (𝓝 ((x : ℂ) ^ (-s))) := by
  unfold Hf
  have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => cexp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * (s - k / 2) ^ 2))
      atTop (𝓝 (cexp (((0 : ℝ) : ℂ) * (s - k / 2) ^ 2))) := by
    apply (Complex.continuous_exp.tendsto _).comp
    exact ((Complex.continuous_ofReal.tendsto 0).comp h0).mul_const _
  simp only [ofReal_zero, zero_mul, Complex.exp_zero] at h1
  simpa using h1.mul_const ((x : ℂ) ^ (-s))

lemma Psi_line_cont (F : ℂ → ℂ) (hF : Differentiable ℂ F) (k : ℝ) (C a0 : ℂ) (t : ℝ)
    (ht0 : t ≠ 0) (htk : t ≠ k) : Continuous (fun y : ℝ => Psi F k C a0 (t + y * I)) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  refine ContinuousAt.comp (g := Psi F k C a0) (f := fun y : ℝ => (t : ℂ) + y * I) ?_
    (by fun_prop)
  apply Psi_contAt F hF
  · intro h; have := congrArg Complex.re h; simp at this; exact ht0 this
  · intro h; have := congrArg Complex.re h; simp at this; exact htk this

lemma Psi_lineA (F : ℂ → ℂ) (k : ℝ) (C a0 : ℂ) (hC : C * C = 1)
    (hFE : ∀ s, F (k - s) = C * F s) (σ y : ℝ) :
    Psi F k C a0 ((k - σ : ℝ) + y * I) = C * Psi F k C a0 (σ + (-y : ℝ) * I) := by
  rw [← Psi_fe F k C a0 hC hFE]
  congr 1; push_cast; ring

/-- limit `ε → 0` of `eps_identity` -/
lemma line_identity (F : ℂ → ℂ) (hF : Differentiable ℂ F) (k : ℝ) (hk : 0 < k) (C a0 : ℂ)
    (hC : C * C = 1) (hFE : ∀ s, F (k - s) = C * F s)
    (σ : ℝ) (hσ : k < σ) (M : ℝ) (hM : ∀ s : ℂ, k - σ ≤ s.re → s.re ≤ σ → ‖F s‖ ≤ M)
    (K : ℝ) (hK : ∀ y : ℝ, ‖Psi F k C a0 (σ + y * I)‖ ≤ K * (1 + y ^ 2)⁻¹)
    (x : ℝ) (hx : 0 < x) :
    I * (∫ y : ℝ, Psi F k C a0 (σ + y * I) * (x : ℂ) ^ (-((σ : ℂ) + y * I))) -
      I * (∫ y : ℝ, Psi F k C a0 ((k - σ : ℝ) + y * I) * (x : ℂ) ^ (-(((k - σ : ℝ) : ℂ) + y * I))) =
      2 * π * I * (-a0 + C * a0 * (x : ℂ) ^ (-(k : ℂ))) := by
  have hC1 : ‖C‖ = 1 := by
    have : ‖C‖ * ‖C‖ = 1 := by rw [← norm_mul, hC, norm_one]
    nlinarith [norm_nonneg C]
  set W := Real.exp ((σ - k / 2) ^ 2) * (x ^ (-σ) + x ^ (-(k - σ))) with hW
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n => by simp only [hεdef]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [hεdef]; rw [div_le_one (by positivity)]; have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); linarith
  have hbound := (integrable_inv_one_add_sq.const_mul K).mul_const W
  -- line σ
  have hB : Tendsto (fun n => ∫ y : ℝ, Psi F k C a0 (σ + y * I) * Hf k x (ε n) (σ + y * I)) atTop
      (𝓝 (∫ y : ℝ, Psi F k C a0 (σ + y * I) * (x : ℂ) ^ (-((σ : ℂ) + y * I)))) := by
    refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hbound (fun n => ?_) ?_
    · exact ((Psi_line_cont F hF k C a0 σ (by linarith) hσ.ne').mul
        ((Hf_diff k x (ε n) hx).continuous.comp (by fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      rw [norm_mul]
      exact mul_le_mul (hK y) (Hf_unif k x (ε n) σ hx (hε0 n).le (hε1 n) _ (by simp; linarith)
        (by simp)) (norm_nonneg _) ((norm_nonneg _).trans (hK y))
    · exact Eventually.of_forall fun y => (Hf_tendsto k x _).const_mul _
  have hA : Tendsto (fun n => ∫ y : ℝ, Psi F k C a0 ((k - σ : ℝ) + y * I) *
      Hf k x (ε n) ((k - σ : ℝ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, Psi F k C a0 ((k - σ : ℝ) + y * I) *
        (x : ℂ) ^ (-(((k - σ : ℝ) : ℂ) + y * I)))) := by
    refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hbound (fun n => ?_) ?_
    · exact ((Psi_line_cont F hF k C a0 (k - σ) (by linarith) (by linarith)).mul
        ((Hf_diff k x (ε n) hx).continuous.comp (by fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      rw [norm_mul, Psi_lineA F k C a0 hC hFE, norm_mul, hC1, one_mul]
      have h3 := hK (-y)
      rw [neg_sq] at h3
      exact mul_le_mul h3 (Hf_unif k x (ε n) σ hx (hε0 n).le (hε1 n) _ (by simp)
        (by simp; linarith)) (norm_nonneg _) ((norm_nonneg _).trans h3)
    · exact Eventually.of_forall fun y => (Hf_tendsto k x _).const_mul _
  have hL := ((hB.const_mul I).sub (hA.const_mul I))
  have hR : Tendsto (fun n => 2 * π * I * (-a0 * Hf k x (ε n) 0 + C * a0 * Hf k x (ε n) k)) atTop
      (𝓝 (2 * π * I * (-a0 * (x : ℂ) ^ (-(0 : ℂ)) + C * a0 * (x : ℂ) ^ (-(k : ℂ))))) :=
    (((Hf_tendsto k x 0).const_mul (-a0)).add ((Hf_tendsto k x k).const_mul (C * a0))).const_mul _
  have heq : ∀ n, I * (∫ y : ℝ, Psi F k C a0 (σ + y * I) * Hf k x (ε n) (σ + y * I)) -
      I * (∫ y : ℝ, Psi F k C a0 ((k - σ : ℝ) + y * I) * Hf k x (ε n) ((k - σ : ℝ) + y * I)) =
      2 * π * I * (-a0 * Hf k x (ε n) 0 + C * a0 * Hf k x (ε n) k) :=
    fun n => eps_identity F hF k hk C a0 hC hFE σ hσ M hM K hK x hx (ε n) (hε0 n)
  have := tendsto_nhds_unique (hL.congr heq) hR
  rw [this]
  simp

end Gelbart

open Complex Real Filter Topology Set MeasureTheory

namespace Gelbart
open GelbartJ

lemma cpow_swap (x : ℝ) (hx : 0 < x) (k σ y : ℝ) :
    (x : ℂ) ^ (-(((k - σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)) =
      (x : ℂ) ^ (-(k : ℂ)) * (((1 / x : ℝ)) : ℂ) ^ (-((σ : ℂ) + y * I)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have harg : (x : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  rw [show (((1 / x : ℝ)) : ℂ) = (x : ℂ)⁻¹ by push_cast; ring, Complex.inv_cpow _ _ harg,
    Complex.cpow_neg (x : ℂ) ((σ : ℂ) + y * I), inv_inv, ← Complex.cpow_add _ _ hx0]
  congr 1; push_cast; ring

theorem axis_identity (a : ℕ → ℂ) (c h k : ℝ) (C : ℂ)
    (hc : 0 < c) (hh : 0 < h) (hk : 0 < k) (hC : C = 1 ∨ C = -1)
    (hgrowth : HeckeCoeffGrowth a c) (hN : HeckeNice a h k C (c + 1)) :
    ∀ t : ℝ, 0 < t → phi a h (1 / t) = C * ((t ^ k : ℝ) : ℂ) * phi a h t := by
  obtain ⟨F, hFd, hFeq, hFb, hFE⟩ := hN
  obtain ⟨K0, _, m, hKc⟩ := coeff_bound a c hc hgrowth
  set a0 := a 0 with ha0
  have hC2 : C * C = 1 := by rcases hC with rfl | rfl <;> norm_num
  set σ := c + 1 + k with hσdef
  have hσk : k < σ := by linarith
  have hσc : c + 1 < σ := by linarith
  obtain ⟨M, hM⟩ := hFb (k - σ) σ
  have hΦ : ∀ y : ℝ, Psi F k C a0 (σ + y * I) = heckeCompletedLSeries a h (σ + y * I) := by
    intro y
    unfold Psi
    rw [hFeq _ (by simp; linarith)]
    ring
  obtain ⟨K, hK⟩ := Phi_line_bound a c h hc hh hgrowth hσc
  have hK' : ∀ y : ℝ, ‖Psi F k C a0 (σ + y * I)‖ ≤ K * (1 + y ^ 2)⁻¹ := by
    intro y; rw [hΦ]; exact hK y
  set g : ℝ → ℂ := fun t => phi a h t - a0 with hg
  have hmel : ∀ y : ℝ, mellin g (σ + y * I) = Psi F k C a0 (σ + y * I) := by
    intro y
    rw [hΦ]
    exact (mellin_phi_sub a c h hc hh hgrowth K0 (‖a 0‖) m hKc (by simp; linarith)).2
  have hvert : Complex.VerticalIntegrable (mellin g) σ := by
    unfold Complex.VerticalIntegrable
    simp_rw [hmel]
    exact Integrable.mono' (integrable_inv_one_add_sq.const_mul K)
      (Psi_line_cont F hFd k C a0 σ (by linarith) hσk.ne').aestronglyMeasurable
      (Eventually.of_forall hK')
  have hconv : MellinConvergent g (σ : ℂ) :=
    mellinConvergent_phi_sub a c h hc hh hgrowth K0 (‖a 0‖) m hKc hσc
  -- A x = 2π g x
  have hA : ∀ x : ℝ, 0 < x →
      (∫ y : ℝ, Psi F k C a0 (σ + y * I) * (x : ℂ) ^ (-((σ : ℂ) + y * I))) = 2 * π * g x := by
    intro x hx
    have hcont : ContinuousAt g x := by
      have := (continuousOn_phi a h hh K0 (‖a 0‖) m hKc).continuousAt (Ioi_mem_nhds hx)
      exact this.sub continuousAt_const
    have hinv := mellinInv_mellin_eq σ g hx hconv hvert hcont
    rw [← hinv]
    unfold mellinInv
    simp_rw [hmel, smul_eq_mul]
    have hπ : (2 * π : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    rw [Complex.real_smul]
    push_cast
    rw [← mul_assoc, mul_one_div_cancel hπ, one_mul]
    congr 1; funext y; ring
  have hB : ∀ x : ℝ, 0 < x →
      (∫ y : ℝ, Psi F k C a0 ((k - σ : ℝ) + y * I) * (x : ℂ) ^ (-(((k - σ : ℝ) : ℂ) + y * I))) =
        C * (x : ℂ) ^ (-(k : ℂ)) * (2 * π * g (1 / x)) := by
    intro x hx
    rw [← hA (1 / x) (by positivity), ← integral_const_mul]
    rw [← integral_neg_eq_self]
    congr 1; funext y
    rw [Psi_lineA F k C a0 hC2 hFE σ (-y), cpow_swap x hx k σ y, neg_neg]
    push_cast
    ring
  intro t ht
  have ht' : 0 < 1 / t := by positivity
  have key := line_identity F hFd k hk C a0 hC2 hFE σ hσk M hM K hK' (1 / t) ht'
  rw [hA _ ht', hB _ ht'] at key
  have hpow : (((1 / t : ℝ)) : ℂ) ^ (-(k : ℂ)) = ((t ^ k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [Real.rpow_neg (by positivity), one_div, Real.inv_rpow ht.le, inv_inv]
  rw [hpow, show 1 / (1 / t) = t by field_simp] at key
  simp only [hg] at key
  have hI : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  have : 2 * π * I * (phi a h (1 / t) - C * ((t ^ k : ℝ) : ℂ) * phi a h t) = 0 := by
    linear_combination key
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hI
  · linear_combination h0

end Gelbart

open Complex Real Filter Topology Set MeasureTheory

namespace Gelbart
open GelbartJ

lemma heckeForm_diffOn (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) :
    DifferentiableOn ℂ (heckeForm a h) {z : ℂ | 0 < z.im} := by
  obtain ⟨K, _, m, hK⟩ := coeff_bound a c hc hgrowth
  intro z0 hz0
  have hz0' : 0 < z0.im := hz0
  set δ := z0.im / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set V : Set ℂ := {z : ℂ | δ < z.im} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_im
  have hz0V : z0 ∈ V := by show δ < z0.im; linarith
  have hd : DifferentiableOn ℂ (fun w => ∑' n : ℕ, a n * cexp (2 * π * I * n * w / h)) V := by
    apply differentiableOn_tsum_of_summable_norm
      (summable_bound K (‖a 0‖) m (by positivity : 0 < 2 * π * δ / h))
    · intro n; fun_prop
    · exact hVo
    · intro n w hw
      have hw' : δ < w.im := hw
      rw [norm_mul, Complex.norm_exp]
      apply mul_le_mul (hK n) _ (Real.exp_pos _).le ((norm_nonneg _).trans (hK n))
      apply Real.exp_le_exp.2
      have : (2 * π * I * n * w / h).re = -(2 * π * n / h) * w.im := by
        simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
        field_simp
      rw [this]
      have h1 : 0 ≤ 2 * π * n / h := by positivity
      have : (2 * π * δ / h) * n = (2 * π * n / h) * δ := by ring
      nlinarith
  exact (hd.differentiableAt (hVo.mem_nhds hz0V)).differentiableWithinAt

theorem automorphic_of_axis (a : ℕ → ℂ) (c h k : ℝ) (C : ℂ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c)
    (hax : ∀ t : ℝ, 0 < t → phi a h (1 / t) = C * ((t ^ k : ℝ) : ℂ) * phi a h t) :
    HeckeAutomorphic a h k C := by
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hD := heckeForm_diffOn a c h hc hh hgrowth
  have hmap : MapsTo (fun z : ℂ => -1 / z) U U := by
    intro z hz
    have hz' : 0 < z.im := hz
    show 0 < (-1 / z).im
    have : 0 < Complex.normSq z := Complex.normSq_pos.2 (by intro h; rw [h] at hz'; simp at hz')
    have e : (-1 / z).im = z.im / Complex.normSq z := by
      rw [Complex.div_im]; simp; ring
    rw [e]; exact div_pos hz' this
  have hf : DifferentiableOn ℂ (fun z => heckeForm a h (-1 / z)) U := by
    refine hD.comp ?_ hmap
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp [hU] at hz
    exact (DifferentiableAt.div (differentiableAt_const _) differentiableAt_id hz0).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z => C * (z / I) ^ (k : ℂ) * heckeForm a h z) U := by
    refine DifferentiableOn.mul ?_ hD
    intro z hz
    have hz' : 0 < z.im := hz
    have hslit : z / I ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left
      simpa using hz'
    apply DifferentiableAt.differentiableWithinAt
    exact ((differentiableAt_id.div_const I).cpow_const hslit).const_mul C
  have hI : I ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] I,
      heckeForm a h (-1 / z) = C * (z / I) ^ (k : ℂ) * heckeForm a h z := by
    have ht : Tendsto (fun t : ℝ => I * t) (𝓝[≠] (1 : ℝ)) (𝓝[≠] I) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun t : ℝ => I * t) (𝓝 1) (𝓝 (I * ((1 : ℝ) : ℂ))) :=
          ((continuous_const.mul Complex.continuous_ofReal).tendsto 1)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        intro h
        apply ht
        have := congrArg Complex.im h
        simpa using this
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t htp
    have e1 : (-1 / (I * (t : ℂ))) = I * ((1 / t : ℝ) : ℂ) := by
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast htp.ne'
      push_cast
      field_simp
      rw [Complex.I_sq]
    have e2 : (I * (t : ℂ) / I) ^ (k : ℂ) = ((t ^ k : ℝ) : ℂ) := by
      rw [mul_div_cancel_left₀ _ Complex.I_ne_zero, Complex.ofReal_cpow htp.le]
    rw [e1, e2]
    have := hax t htp
    unfold phi at this
    exact this
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (hf.analyticOnNhd hUo)
    (hg.analyticOnNhd hUo) (convex_halfSpace_im_gt 0).isPreconnected hI hfreq
  intro z hz
  exact heq hz

end Gelbart

namespace Gelbart

theorem _root_.solution
    (a : ℕ → ℂ) (c h k : ℝ) (C : ℂ)
    (hc : 0 < c) (hh : 0 < h) (hk : 0 < k) (hC : C = 1 ∨ C = -1)
    (hgrowth : HeckeCoeffGrowth a c) :
    HeckeNice a h k C (c + 1) → HeckeAutomorphic a h k C := by
  intro hN
  exact automorphic_of_axis a c h k C hc hh hgrowth
    (axis_identity a c h k C hc hh hk hC hgrowth hN)

end Gelbart

