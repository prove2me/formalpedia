-- Prove2me | solution 1 for FedergruenZipkin.AvgCost.lemma5_operators_preserve_V
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T13:22:00.644211+00:00
-- url     : https://prove2.me/submissions/af38e18a-db50-420f-8e46-77c761a33944

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

set_option autoImplicit false
open Filter Topology Asymptotics
open scoped ENNReal

namespace FZ9
open FedergruenZipkin.AvgCost


lemma sym_bound {G : ℝ → ℝ} (hG : AnalyticAt ℝ G 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ θ : ℝ, |θ| ≤ δ → |G θ + G (-θ) - 2 * G 0| ≤ C * θ ^ 2 := by
  obtain ⟨P, hP⟩ := hG
  have h0 : P.coeff 0 = G 0 := hP.coeff_zero 1
  have hbig := hP.isBigO_sub_partialSum_pow 2
  obtain ⟨C, hCpos, hC⟩ := hbig.exists_pos
  rw [Asymptotics.IsBigOWith] at hC
  rw [Metric.eventually_nhds_iff] at hC
  obtain ⟨ε, hε, hball⟩ := hC
  refine ⟨2 * C, ε / 2, by positivity, ?_⟩
  intro θ hθ
  have h1 := hball (y := θ) (by rw [Real.dist_eq]; simp; linarith)
  have h2 := hball (y := -θ) (by rw [Real.dist_eq]; simp; linarith)
  have ps : ∀ y : ℝ, P.partialSum 2 y = P.coeff 0 + y * P.coeff 1 := by
    intro y
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  have h1' : |G θ - (G 0 + θ * P.coeff 1)| ≤ C * θ ^ 2 := by
    have := h1
    simp only [zero_add, ps, h0, Real.norm_eq_abs, abs_abs, abs_pow, sq_abs] at this
    exact this
  have h2' : |G (-θ) - (G 0 + (-θ) * P.coeff 1)| ≤ C * θ ^ 2 := by
    have := h2
    simp only [zero_add, ps, h0, Real.norm_eq_abs, abs_abs, abs_pow, sq_abs, abs_neg, neg_sq] at this
    exact this
  have e : G θ + G (-θ) - 2 * G 0
      = (G θ - (G 0 + θ * P.coeff 1)) + (G (-θ) - (G 0 + (-θ) * P.coeff 1)) := by ring
  rw [e]
  calc |(G θ - (G 0 + θ * P.coeff 1)) + (G (-θ) - (G 0 + (-θ) * P.coeff 1))|
      ≤ |G θ - (G 0 + θ * P.coeff 1)| + |G (-θ) - (G 0 + (-θ) * P.coeff 1)| := abs_add_le _ _
    _ ≤ C * θ ^ 2 + C * θ ^ 2 := add_le_add h1' h2'
    _ = 2 * C * θ ^ 2 := by ring


noncomputable def cser (p : ℕ → ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  ∑' j : ℕ, p j * (j:ℝ)^m * Real.cos ((j:ℝ) * θ)
noncomputable def sser (p : ℕ → ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  ∑' j : ℕ, p j * (j:ℝ)^m * Real.sin ((j:ℝ) * θ)

lemma cser_neg (p : ℕ → ℝ) (m : ℕ) (θ : ℝ) : cser p m (-θ) = cser p m θ := by
  unfold cser
  congr 1; ext j
  rw [mul_neg, Real.cos_neg]

lemma cser_zero (p : ℕ → ℝ) (m : ℕ) : cser p m 0 = ∑' j : ℕ, p j * (j:ℝ)^m := by
  unfold cser; simp

lemma cs_summable (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (m : ℕ)
    (h : Summable (fun j : ℕ => p j * (j:ℝ)^m)) (f : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) (θ : ℝ) :
    Summable (fun j : ℕ => p j * (j:ℝ)^m * f ((j:ℝ) * θ)) := by
  refine Summable.of_norm_bounded h (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have : 0 ≤ p j * (j:ℝ)^m := mul_nonneg (hp j) (by positivity)
  rw [abs_of_nonneg this]
  calc p j * (j:ℝ)^m * |f ((j:ℝ) * θ)| ≤ p j * (j:ℝ)^m * 1 :=
        mul_le_mul_of_nonneg_left (hf _) this
    _ = _ := mul_one _

lemma cser_deriv (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (m : ℕ)
    (h0 : Summable (fun j : ℕ => p j * (j:ℝ)^m))
    (h1 : Summable (fun j : ℕ => p j * (j:ℝ)^(m+1))) (θ : ℝ) :
    HasDerivAt (cser p m) (-(sser p (m+1) θ)) θ := by
  have key := hasDerivAt_tsum (𝕜 := ℝ) (u := fun j : ℕ => p j * (j:ℝ)^(m+1))
    (g := fun (j : ℕ) (θ : ℝ) => p j * (j:ℝ)^m * Real.cos ((j:ℝ) * θ))
    (g' := fun (j : ℕ) (θ : ℝ) => -(p j * (j:ℝ)^(m+1) * Real.sin ((j:ℝ) * θ)))
    h1 ?_ ?_ ?_ θ (y₀ := 0)
  · unfold sser cser
    rw [tsum_neg] at key
    exact key
  · intro j y
    have := (((hasDerivAt_id y).const_mul (j:ℝ)).cos).const_mul (p j * (j:ℝ)^m)
    refine HasDerivAt.congr_deriv this ?_
    simp only [id, mul_one]
    ring
  · intro j y
    rw [Real.norm_eq_abs, abs_neg, abs_mul]
    have : 0 ≤ p j * (j:ℝ)^(m+1) := mul_nonneg (hp j) (by positivity)
    rw [abs_of_nonneg this]
    calc p j * (j:ℝ)^(m+1) * |Real.sin ((j:ℝ) * y)| ≤ p j * (j:ℝ)^(m+1) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) this
      _ = _ := mul_one _
  · exact cs_summable p hp m h0 Real.cos Real.abs_cos_le_one 0

lemma sser_deriv (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (m : ℕ)
    (h0 : Summable (fun j : ℕ => p j * (j:ℝ)^m))
    (h1 : Summable (fun j : ℕ => p j * (j:ℝ)^(m+1))) (θ : ℝ) :
    HasDerivAt (sser p m) (cser p (m+1) θ) θ := by
  have key := hasDerivAt_tsum (𝕜 := ℝ) (u := fun j : ℕ => p j * (j:ℝ)^(m+1))
    (g := fun (j : ℕ) (θ : ℝ) => p j * (j:ℝ)^m * Real.sin ((j:ℝ) * θ))
    (g' := fun (j : ℕ) (θ : ℝ) => p j * (j:ℝ)^(m+1) * Real.cos ((j:ℝ) * θ))
    h1 ?_ ?_ ?_ θ (y₀ := 0)
  · exact key
  · intro j y
    have := (((hasDerivAt_id y).const_mul (j:ℝ)).sin).const_mul (p j * (j:ℝ)^m)
    refine HasDerivAt.congr_deriv this ?_
    simp only [id, mul_one]
    ring
  · intro j y
    rw [Real.norm_eq_abs, abs_mul]
    have : 0 ≤ p j * (j:ℝ)^(m+1) := mul_nonneg (hp j) (by positivity)
    rw [abs_of_nonneg this]
    calc p j * (j:ℝ)^(m+1) * |Real.cos ((j:ℝ) * y)| ≤ p j * (j:ℝ)^(m+1) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) this
      _ = _ := mul_one _
  · exact cs_summable p hp m h0 Real.sin Real.abs_sin_le_one 0


lemma moment_step (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (m : ℕ)
    (h0 : Summable (fun j : ℕ => p j * (j:ℝ)^m))
    (hA : AnalyticAt ℝ (cser p m) 0) :
    Summable (fun j : ℕ => p j * (j:ℝ)^(m+2)) := by
  obtain ⟨C, δ, hδ, hsym⟩ := sym_bound hA
  have hCs : ∀ θ : ℝ, |θ| ≤ δ → cser p m 0 - cser p m θ ≤ |C| * θ ^ 2 := by
    intro θ hθ
    have h := hsym θ hθ
    rw [cser_neg] at h
    have h2 := (abs_le.1 h).1
    have : C * θ ^ 2 ≤ |C| * θ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
    have := mul_nonneg (abs_nonneg C) (sq_nonneg θ)
    linarith
  have hnn : ∀ j : ℕ, 0 ≤ p j * (j:ℝ)^(m+2) := fun j => mul_nonneg (hp j) (by positivity)
  refine summable_of_sum_range_le hnn (c := 2 * |C| + 2) (fun N => ?_)
  set B : ℝ := ∑ j ∈ Finset.range N, p j * (j:ℝ)^(m+4) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (by positivity))
  set θ : ℝ := min (min δ (1 / ((N:ℝ) + 1))) (1 / (B + 1)) with hθdef
  have hθ0 : 0 < θ := lt_min (lt_min hδ (by positivity)) (by positivity)
  have hθδ : θ ≤ δ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hθN : θ ≤ 1 / ((N:ℝ) + 1) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hθB : θ ≤ 1 / (B + 1) := min_le_right _ _
  have hθ1 : θ ≤ 1 := by
    have : 1 / (B + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  -- upper bound
  have hup : ∑ j ∈ Finset.range N, p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) ≤ |C| * θ ^ 2 := by
    have hs1 : Summable (fun j : ℕ => p j * (j:ℝ)^m * Real.cos ((j:ℝ) * θ)) :=
      cs_summable p hp m h0 Real.cos Real.abs_cos_le_one θ
    have hterm : ∀ j : ℕ, 0 ≤ p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) := fun j =>
      mul_nonneg (mul_nonneg (hp j) (by positivity)) (by linarith [Real.cos_le_one ((j:ℝ) * θ)])
    have hsum : Summable (fun j : ℕ => p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ))) := by
      have := h0.sub hs1
      refine this.congr (fun j => ?_)
      ring
    calc _ ≤ ∑' j : ℕ, p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) :=
          Summable.sum_le_tsum _ (fun j _ => hterm j) hsum
      _ = cser p m 0 - cser p m θ := by
          rw [cser_zero]; unfold cser
          rw [← Summable.tsum_sub h0 hs1]
          congr 1; ext j; ring
      _ ≤ |C| * θ ^ 2 := hCs θ (by rw [abs_of_pos hθ0]; exact hθδ)
  -- lower bound termwise
  have hlow : ∀ j ∈ Finset.range N, θ ^ 2 / 2 * (p j * (j:ℝ)^(m+2)) - θ ^ 4 * (5 / 96) * (p j * (j:ℝ)^(m+4))
      ≤ p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) := by
    intro j hj
    have hjN : (j:ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hj).le
    have hx : |(j:ℝ) * θ| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      calc (j:ℝ) * θ ≤ N * (1 / ((N:ℝ) + 1)) := by
            apply mul_le_mul hjN hθN hθ0.le (by positivity)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]; linarith
    have hc := Real.cos_bound hx
    have hc2 := (abs_le.1 hc).2
    have e4 : |(j:ℝ) * θ| ^ 4 = ((j:ℝ) * θ) ^ 4 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    rw [e4] at hc2
    have hpj : 0 ≤ p j * (j:ℝ)^m := mul_nonneg (hp j) (by positivity)
    have : p j * (j:ℝ)^m * (((j:ℝ) * θ) ^ 2 / 2 - ((j:ℝ) * θ) ^ 4 * (5 / 96))
        ≤ p j * (j:ℝ)^m * (1 - Real.cos ((j:ℝ) * θ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hpj
    calc _ = p j * (j:ℝ)^m * (((j:ℝ) * θ) ^ 2 / 2 - ((j:ℝ) * θ) ^ 4 * (5 / 96)) := by ring
      _ ≤ _ := this
  have hlow' := Finset.sum_le_sum hlow
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hlow'
  rw [← hB] at hlow'
  set A : ℝ := ∑ j ∈ Finset.range N, p j * (j:ℝ)^(m+2) with hAdef
  have hcomb : θ ^ 2 / 2 * A - θ ^ 4 * (5 / 96) * B ≤ |C| * θ ^ 2 := le_trans hlow' hup
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hBθ : θ ^ 2 * B ≤ 1 := by
    have h1 : θ * B ≤ 1 := by
      calc θ * B ≤ 1 / (B + 1) * B := mul_le_mul_of_nonneg_right hθB hB0
        _ ≤ 1 := by
          rw [one_div, inv_mul_le_iff₀ (by positivity)]; linarith
    calc θ ^ 2 * B = θ * (θ * B) := by ring
      _ ≤ 1 * 1 := mul_le_mul hθ1 h1 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have : A ≤ 2 * |C| + 2 := by
    have h3 : θ ^ 2 * (A / 2 - θ ^ 2 * (5 / 96) * B - |C|) ≤ 0 := by nlinarith
    have h4 : A / 2 - θ ^ 2 * (5 / 96) * B - |C| ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have := mul_pos hθ2 hcon
      linarith
    nlinarith
  exact this


lemma F_analytic (M : FedergruenZipkin.AvgCost.Model) : AnalyticAt ℝ (cser M.p 0) 0 := by
  have hA := (Complex.reCLM.analyticAt _).comp M.charfun_analytic
  convert hA using 1
  funext θ
  simp only [Function.comp]
  have hs : Summable (fun j : ℕ => ((M.p j : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) * (j : ℂ))) := by
    refine Summable.of_norm_bounded M.p_sum.summable (fun j => ?_)
    have e : Complex.I * (θ : ℂ) * (j : ℂ) = (((θ * j : ℝ)) : ℂ) * Complex.I := by push_cast; ring
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (M.p_nonneg j))
  rw [Complex.reCLM_apply, Complex.re_tsum hs]
  unfold cser
  congr 1; ext j
  have e : Complex.I * (θ : ℂ) * (j : ℂ) = (((θ * j : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simp [mul_comm]

lemma moments_aux (M : FedergruenZipkin.AvgCost.Model) (k : ℕ) :
    Summable (fun j : ℕ => M.p j * (j:ℝ)^(2*k)) ∧
    deriv^[2*k] (cser M.p 0) = fun θ => (-1:ℝ)^k * cser M.p (2*k) θ := by
  induction k with
  | zero =>
    refine ⟨by simpa using M.p_sum.summable, ?_⟩
    funext θ
    simp
  | succ k ih =>
    obtain ⟨hS, hD⟩ := ih
    have hp := M.p_nonneg
    have hGA : AnalyticAt ℝ (deriv^[2*k] (cser M.p 0)) 0 := (F_analytic M).iterated_deriv (2*k)
    have hCA : AnalyticAt ℝ (cser M.p (2*k)) 0 := by
      have : cser M.p (2*k) = fun θ => (-1:ℝ)^k * (deriv^[2*k] (cser M.p 0)) θ := by
        rw [hD]; funext θ
        rw [← mul_assoc, ← mul_pow]; simp
      rw [this]
      exact analyticAt_const.mul hGA
    have S2 := moment_step M.p hp (2*k) hS hCA
    have S1 : Summable (fun j : ℕ => M.p j * (j:ℝ)^(2*k+1)) := by
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hp j) (by positivity)) (fun j => ?_) (hS.add S2)
      have hx : 0 ≤ (j:ℝ)^(2*k) := by positivity
      have : (j:ℝ)^(2*k+1) ≤ (j:ℝ)^(2*k) + (j:ℝ)^(2*k+2) := by
        rw [pow_succ, pow_add]
        nlinarith [sq_nonneg ((j:ℝ) - 1), mul_nonneg hx (sq_nonneg ((j:ℝ) - 1))]
      calc M.p j * (j:ℝ)^(2*k+1) ≤ M.p j * ((j:ℝ)^(2*k) + (j:ℝ)^(2*k+2)) :=
            mul_le_mul_of_nonneg_left this (hp j)
        _ = _ := by ring
    have S2' : Summable (fun j : ℕ => M.p j * (j:ℝ)^(2*k+1+1)) := S2
    have e : 2*(k+1) = 2*k+1+1 := by ring
    rw [e]
    refine ⟨S2', ?_⟩
    have d1 : deriv (deriv^[2*k] (cser M.p 0)) = fun θ => (-1:ℝ)^k * (-(sser M.p (2*k+1) θ)) := by
      rw [hD]; funext θ
      exact (((cser_deriv M.p hp (2*k) hS S1 θ).const_mul ((-1:ℝ)^k))).deriv
    have d2 : deriv (deriv (deriv^[2*k] (cser M.p 0))) = fun θ => (-1:ℝ)^(k+1) * cser M.p (2*k+1+1) θ := by
      rw [d1]; funext θ
      have := ((sser_deriv M.p hp (2*k+1) S1 S2' θ).neg.const_mul ((-1:ℝ)^k)).deriv
      exact this.trans (by ring)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact d2


/-- All moments of the demand are finite (consequence of Assumption 2, analytic characteristic function). -/
theorem moments_finite (M : FedergruenZipkin.AvgCost.Model) (k : ℕ) :
    Summable (fun j : ℕ => M.p j * (j:ℝ)^k) := by
  have h2 := (moments_aux M k).1
  have h1 := M.p_sum.summable
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (M.p_nonneg j) (by positivity)) (fun j => ?_) (h2.add h1)
  have hp := M.p_nonneg j
  have : (j:ℝ)^k ≤ (j:ℝ)^(2*k) + 1 := by
    rcases le_or_gt (j:ℝ) 1 with h | h
    · have : (j:ℝ)^k ≤ 1 := pow_le_one₀ (by positivity) h
      have : 0 ≤ (j:ℝ)^(2*k) := by positivity
      linarith
    · have : (j:ℝ)^k ≤ (j:ℝ)^(2*k) := pow_le_pow_right₀ h.le (by omega)
      linarith
  calc M.p j * (j:ℝ)^k ≤ M.p j * ((j:ℝ)^(2*k) + 1) := mul_le_mul_of_nonneg_left this hp
    _ = _ := by ring


lemma abs_sub_pow_le (y : ℝ) (j : ℕ) (n : ℕ) :
    |y - (j:ℝ)| ^ n ≤ 2 ^ n * (|y| ^ n + (j:ℝ) ^ n) := by
  have h1 : |y - (j:ℝ)| ≤ |y| + (j:ℝ) := by
    calc |y - (j:ℝ)| ≤ |y| + |(j:ℝ)| := abs_sub _ _
      _ = _ := by rw [Nat.abs_cast]
  have h2 : |y| + (j:ℝ) ≤ 2 * max |y| (j:ℝ) := by
    have := le_max_left |y| (j:ℝ)
    have := le_max_right |y| (j:ℝ)
    linarith
  have h3 : |y - (j:ℝ)| ^ n ≤ (2 * max |y| (j:ℝ)) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) n
  have h4 : (max |y| (j:ℝ)) ^ n ≤ |y| ^ n + (j:ℝ) ^ n := by
    rcases le_total |y| (j:ℝ) with h | h
    · rw [max_eq_right h]; have : 0 ≤ |y| ^ n := by positivity
      linarith
    · rw [max_eq_left h]; have : 0 ≤ (j:ℝ) ^ n := by positivity
      linarith
  calc |y - (j:ℝ)| ^ n ≤ (2 * max |y| (j:ℝ)) ^ n := h3
    _ = 2 ^ n * (max |y| (j:ℝ)) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (|y| ^ n + (j:ℝ) ^ n) := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem summable_poly (M : FedergruenZipkin.AvgCost.Model) (n : ℕ) (A B : ℝ) (U : ℤ) (v : ℤ → ℝ)
    (hv : ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ n) (y : ℤ) (hy : y ≤ U) :
    Summable (fun j : ℕ => M.p j * v (y - j)) := by
  have hp := M.p_nonneg
  have hn := moments_finite M n
  have hs := M.p_sum.summable
  have key : Summable (fun j : ℕ => M.p j * |A| + |B| * 2 ^ n * (|(y:ℝ)| ^ n * M.p j + M.p j * (j:ℝ) ^ n)) :=
    (hs.mul_right _).add (((hs.mul_left (|(y:ℝ)| ^ n)).add hn).mul_left _)
  refine Summable.of_norm_bounded key (fun j => ?_)
  have hyj : y - (j:ℤ) ≤ U := by omega
  have h1 := hv (y - j) hyj
  have h2 := abs_sub_pow_le (y:ℝ) j n
  have hc : ((y - (j:ℤ) : ℤ) : ℝ) = (y:ℝ) - (j:ℝ) := by push_cast; ring
  rw [hc] at h1
  have h3 : |v (y - j)| ≤ |A| + |B| * (2 ^ n * (|(y:ℝ)| ^ n + (j:ℝ) ^ n)) := by
    calc |v (y - j)| ≤ A + B * |(y:ℝ) - (j:ℝ)| ^ n := h1
      _ ≤ |A| + |B| * |(y:ℝ) - (j:ℝ)| ^ n := by
          have := le_abs_self A
          have : B * |(y:ℝ) - (j:ℝ)| ^ n ≤ |B| * |(y:ℝ) - (j:ℝ)| ^ n :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
          linarith
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
          linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp j)]
  calc M.p j * |v (y - j)| ≤ M.p j * (|A| + |B| * (2 ^ n * (|(y:ℝ)| ^ n + (j:ℝ) ^ n))) :=
        mul_le_mul_of_nonneg_left h3 (hp j)
    _ = _ := by ring



lemma pos_prop {f : ℤ → ℝ} {U : ℤ} (hc : ∀ x, x + 1 ≤ U → f x - f (x-1) ≤ f (x+1) - f x)
    {y : ℤ} (h : 0 < f (y+1) - f y) : ∀ n, y ≤ n → n + 1 ≤ U → 0 < f (n+1) - f n := by
  intro n hn
  induction n, hn using Int.le_induction with
  | base => intro _; exact h
  | succ n hn ih =>
    intro hU
    have h1 := ih (by omega)
    have h2 := hc (n+1) (by omega)
    have e : n + 1 - 1 = n := by ring
    rw [e] at h2
    linarith

lemma conv_mono_above {f : ℤ → ℝ} {U : ℤ}
    (hc : ∀ x, x + 1 ≤ U → f x - f (x-1) ≤ f (x+1) - f x)
    {s : ℤ} (hs : ∀ z ≤ U, f s ≤ f z) (hsU : s ≤ U) :
    ∀ a b, s ≤ a → a ≤ b → b ≤ U → f a ≤ f b := by
  have key : ∀ y, s ≤ y → y + 1 ≤ U → f y ≤ f (y+1) := by
    intro y hy
    induction y, hy using Int.le_induction with
    | base => intro hU; exact hs _ hU
    | succ n hn ih =>
      intro hU
      have h1 := ih (by omega)
      have h2 := hc (n+1) (by omega)
      have e : n + 1 - 1 = n := by ring
      rw [e] at h2
      linarith
  intro a b ha hab hb
  revert hb
  induction b, hab using Int.le_induction with
  | base => intro _; exact le_rfl
  | succ n hn ih =>
    intro hU
    exact le_trans (ih (by omega)) (key n (by omega) hU)

lemma conv_anti_below {f : ℤ → ℝ} {U : ℤ}
    (hc : ∀ x, x + 1 ≤ U → f x - f (x-1) ≤ f (x+1) - f x)
    {s : ℤ} (hs : ∀ z ≤ U, f s ≤ f z) (hsU : s ≤ U) :
    ∀ a b, a ≤ b → b ≤ s → f b ≤ f a := by
  have key : ∀ y, y + 1 ≤ s → f (y+1) ≤ f y := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    have h := pos_prop hc (y := y) (by linarith) (s-1) (by omega) (by omega)
    have e : s - 1 + 1 = s := by ring
    rw [e] at h
    have := hs (s-1) (by omega)
    linarith
  intro a b hab
  induction b, hab using Int.le_induction with
  | base => intro _; exact le_rfl
  | succ n hn ih =>
    intro hU
    exact le_trans (key n (by omega)) (ih (by omega))

lemma R_convex (M : Model) (U : ℤ) (v : ℤ → ℝ) (hconv : ConvexBelow U v)
    (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) :
    ∀ y, y + 1 ≤ U → R M v y - R M v (y-1) ≤ R M v (y+1) - R M v y := by
  intro y hy
  have hG := M.G_convex y
  have s0 := hsum y (by omega)
  have s1 := hsum (y-1) (by omega)
  have s2 := hsum (y+1) hy
  have key : ∑' j : ℕ, M.p j * v (y - j) - ∑' j : ℕ, M.p j * v (y - 1 - j)
      ≤ ∑' j : ℕ, M.p j * v (y + 1 - j) - ∑' j : ℕ, M.p j * v (y - j) := by
    rw [← Summable.tsum_sub s0 s1, ← Summable.tsum_sub s2 s0]
    refine Summable.tsum_le_tsum (fun j => ?_) (s0.sub s1) (s2.sub s0)
    have h := hconv (y - j) (by have : (0:ℤ) ≤ j := by positivity
                                omega)
    have e1 : y - (j:ℤ) - 1 = y - 1 - j := by ring
    have e2 : y - (j:ℤ) + 1 = y + 1 - j := by ring
    rw [e1, e2] at h
    have hp := M.p_nonneg j
    nlinarith
  unfold R
  linarith

lemma G_anti (M : Model) (yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) :
    ∀ y, y < yInf → M.G (y+1) ≤ M.G y := by
  intro y hy
  by_contra hcon
  push_neg at hcon
  have hc : ∀ x, x + 1 ≤ yInf → M.G x - M.G (x-1) ≤ M.G (x+1) - M.G x := fun x _ => M.G_convex x
  have h := pos_prop hc (y := y) (by linarith) (yInf - 1) (by omega) (by omega)
  have e : yInf - 1 + 1 = yInf := by ring
  rw [e] at h
  have := hyInf.1 (yInf - 1)
  linarith [this]

lemma R_anti (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (v : ℤ → ℝ) (hmono : ∀ x, x < yInf → v (x + 1) ≤ v x)
    (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) :
    ∀ y, y < yInf → R M v (y+1) ≤ R M v y := by
  intro y hy
  have s0 := hsum y (by omega)
  have s2 := hsum (y+1) (by omega)
  unfold R
  have hG := G_anti M yInf hyInf y hy
  have : ∑' j : ℕ, M.p j * v (y + 1 - j) ≤ ∑' j : ℕ, M.p j * v (y - j) := by
    refine Summable.tsum_le_tsum (fun j => ?_) s2 s0
    have h := hmono (y - j) (by have : (0:ℤ) ≤ j := by positivity
                                omega)
    have e2 : y - (j:ℤ) + 1 = y + 1 - j := by ring
    rw [e2] at h
    exact mul_le_mul_of_nonneg_left h (M.p_nonneg j)
  linarith

theorem critNum_attains (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U) (g : ℝ) (v : ℤ → ℝ)
    (hv : InV M U yInf v) (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j)))
    (hopt : OptEq M U g v) :
    ∃ ystar : ℤ, ystar ≤ U ∧ yInf ≤ ystar ∧ (∀ x ≤ U, v ystar ≤ v x) ∧
      Feasible M U (critNum M ystar) ∧ ∀ x ≤ U, g + v x = R M v (critNum M ystar x) := by
  obtain ⟨_, hmono, hconv⟩ := hv
  have hRc := R_convex M U v hconv hsum
  have hRa := R_anti M U yInf hyInf hU v hmono hsum
  -- global minimizer over y ≤ U lies in [yInf, U]
  have hanti : ∀ y, y ≤ yInf → R M v yInf ≤ R M v y := by
    intro y hy
    induction y, hy using Int.le_induction_down with
    | base => exact le_rfl
    | pred n hn ih =>
      have := hRa (n-1) (by omega)
      rw [sub_add_cancel] at this
      exact le_trans ih this
  let S : Finset ℤ := (Finset.Icc yInf U).filter (fun y => ∀ z ∈ Finset.Icc yInf U, R M v y ≤ R M v z)
  have hne : S.Nonempty := by
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc yInf U) (R M v)
      ⟨yInf, Finset.mem_Icc.2 ⟨le_rfl, hU⟩⟩
    exact ⟨m, Finset.mem_filter.2 ⟨hm, hmin⟩⟩
  set ys := S.min' hne with hys
  have hysS : ys ∈ S := Finset.min'_mem S hne
  have hysI := (Finset.mem_filter.1 hysS).1
  have hysmin := (Finset.mem_filter.1 hysS).2
  have hys1 : yInf ≤ ys := (Finset.mem_Icc.1 hysI).1
  have hys2 : ys ≤ U := (Finset.mem_Icc.1 hysI).2
  have hglob : ∀ z ≤ U, R M v ys ≤ R M v z := by
    intro z hz
    by_cases h : yInf ≤ z
    · exact hysmin z (Finset.mem_Icc.2 ⟨h, hz⟩)
    · have := hanti z (by omega)
      exact le_trans (hysmin yInf (Finset.mem_Icc.2 ⟨le_rfl, hU⟩)) this
  have hmonoR := conv_mono_above hRc hglob hys2
  have hantiR := conv_anti_below hRc hglob hys2
  -- OptEq at ys
  have hvys : g + v ys = R M v ys := by
    obtain ⟨hle, y, hy1, hy2, hy3, heq⟩ := hopt ys hys2
    have := hglob y hy3
    have h2 := hle ys le_rfl (by have := M.b_pos; omega) hys2
    linarith
  have hvmin : ∀ x ≤ U, v ys ≤ v x := by
    intro x hx
    obtain ⟨_, y, hy1, hy2, hy3, heq⟩ := hopt x hx
    have := hglob y hy3
    linarith
  have hfeas : Feasible M U (critNum M ys) := by
    intro x hx
    unfold critNum
    have := M.b_pos
    refine ⟨le_max_left _ _, ?_, ?_⟩
    · apply max_le (by omega)
      exact le_trans (min_le_right _ _) le_rfl
    · apply max_le hx
      exact le_trans (min_le_left _ _) hys2
  refine ⟨ys, hys2, hys1, hvmin, hfeas, ?_⟩
  intro x hx
  obtain ⟨hle, y, hy1, hy2, hy3, heq⟩ := hopt x hx
  have hb := M.b_pos
  unfold critNum
  by_cases hxy : ys ≤ x
  · have : max x (min ys (x + M.b)) = x := by
      apply max_eq_left
      exact le_trans (min_le_left _ _) hxy
    rw [this]
    -- R x ≤ R y for y ≥ x ≥ ys
    have := hmonoR x y hxy hy1 hy3
    have h2 := hle x le_rfl (by omega) hx
    linarith
  · push_neg at hxy
    by_cases hb' : ys ≤ x + M.b
    · have : max x (min ys (x + M.b)) = ys := by
        rw [min_eq_left hb']
        exact max_eq_right hxy.le
      rw [this]
      have h2 := hle ys hxy.le hb' hys2
      have := hglob y hy3
      linarith
    · push_neg at hb'
      have : max x (min ys (x + M.b)) = x + M.b := by
        rw [min_eq_right hb'.le]
        exact max_eq_right (by omega)
      rw [this]
      have h2 := hle (x + M.b) (by omega) le_rfl (by omega)
      have h3 := hantiR y (x + M.b) hy2 hb'.le
      linarith


lemma R_min_exists (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (v : ℤ → ℝ) (hv : InV M U yInf v)
    (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) :
    ∃ ys : ℤ, yInf ≤ ys ∧ ys ≤ U ∧ ∀ z ≤ U, R M v ys ≤ R M v z := by
  obtain ⟨_, hmono, hconv⟩ := hv
  have hRa := R_anti M U yInf hyInf hU v hmono hsum
  have hanti : ∀ y, y ≤ yInf → R M v yInf ≤ R M v y := by
    intro y hy
    induction y, hy using Int.le_induction_down with
    | base => exact le_rfl
    | pred n hn ih =>
      have := hRa (n-1) (by omega)
      rw [sub_add_cancel] at this
      exact le_trans ih this
  let S' : Finset ℤ := (Finset.Icc yInf U).filter (fun y => ∀ z ∈ Finset.Icc yInf U, R M v y ≤ R M v z)
  have hne : S'.Nonempty := by
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc yInf U) (R M v)
      ⟨yInf, Finset.mem_Icc.2 ⟨le_rfl, hU⟩⟩
    exact ⟨m, Finset.mem_filter.2 ⟨hm, hmin⟩⟩
  have hysS : S'.min' hne ∈ S' := Finset.min'_mem S' hne
  have hysI := (Finset.mem_filter.1 hysS).1
  have hysmin := (Finset.mem_filter.1 hysS).2
  refine ⟨S'.min' hne, (Finset.mem_Icc.1 hysI).1, (Finset.mem_Icc.1 hysI).2, ?_⟩
  intro z hz
  by_cases h : yInf ≤ z
  · exact hysmin z (Finset.mem_Icc.2 ⟨h, hz⟩)
  · have := hanti z (by omega)
    exact le_trans (hysmin yInf (Finset.mem_Icc.2 ⟨le_rfl, hU⟩)) this

/-- the critical-number policy attains the min of a convex `R` with global min `ys` over `Y(x)` -/
lemma crit_opt (M : Model) (U : ℤ) (R' : ℤ → ℝ)
    (hRc : ∀ y, y + 1 ≤ U → R' y - R' (y-1) ≤ R' (y+1) - R' y)
    {ys : ℤ} (hysU : ys ≤ U) (hglob : ∀ z ≤ U, R' ys ≤ R' z) (x : ℤ) (hx : x ≤ U) :
    (x ≤ critNum M ys x ∧ critNum M ys x ≤ x + M.b ∧ critNum M ys x ≤ U) ∧
    ∀ y, x ≤ y → y ≤ x + M.b → y ≤ U → R' (critNum M ys x) ≤ R' y := by
  have hmonoR := conv_mono_above hRc hglob hysU
  have hantiR := conv_anti_below hRc hglob hysU
  have hb := M.b_pos
  refine ⟨⟨le_max_left _ _, max_le (by omega) (min_le_right _ _), max_le hx (le_trans (min_le_left _ _) hysU)⟩, ?_⟩
  intro y hy1 hy2 hy3
  unfold critNum
  by_cases hxy : ys ≤ x
  · have : max x (min ys (x + M.b)) = x := max_eq_left (le_trans (min_le_left _ _) hxy)
    rw [this]
    exact hmonoR x y hxy hy1 hy3
  · push_neg at hxy
    by_cases hb' : ys ≤ x + M.b
    · have : max x (min ys (x + M.b)) = ys := by
        rw [min_eq_left hb']; exact max_eq_right hxy.le
      rw [this]
      exact hglob y hy3
    · push_neg at hb'
      have : max x (min ys (x + M.b)) = x + M.b := by
        rw [min_eq_right hb'.le]; exact max_eq_right (by omega)
      rw [this]
      exact hantiR y (x + M.b) hy2 hb'.le

lemma S_eq_R (M : Model) (U : ℤ) (v : ℤ → ℝ)
    (hRc : ∀ y, y + 1 ≤ U → R M v y - R M v (y-1) ≤ R M v (y+1) - R M v y)
    {ys : ℤ} (hysU : ys ≤ U) (hglob : ∀ z ≤ U, R M v ys ≤ R M v z) (x : ℤ) (hx : x ≤ U) :
    S M U v x = R M v (critNum M ys x) := by
  obtain ⟨⟨h1, h2, h3⟩, hopt⟩ := crit_opt M U (R M v) hRc hysU hglob x hx
  unfold S
  apply le_antisymm
  · exact ciInf_le (f := fun y : {y : ℤ // x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U} => R M v y)
      ⟨R M v (critNum M ys x), by
        rintro _ ⟨⟨y, hy⟩, rfl⟩
        exact hopt y hy.1 hy.2.1 hy.2.2⟩ ⟨critNum M ys x, h1, h2, h3⟩
  · have : Nonempty {y : ℤ // x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U} := ⟨⟨critNum M ys x, h1, h2, h3⟩⟩
    exact le_ciInf (fun ⟨y, hy⟩ => hopt y hy.1 hy.2.1 hy.2.2)

/-- `x ↦ R (critNum ys x)` is discretely convex on `x ≤ U`. -/
lemma g_convex (M : Model) (U : ℤ) (R' : ℤ → ℝ)
    (hRc : ∀ y, y + 1 ≤ U → R' y - R' (y-1) ≤ R' (y+1) - R' y)
    {ys : ℤ} (hysU : ys ≤ U) (hglob : ∀ z ≤ U, R' ys ≤ R' z) :
    ∀ x, x + 1 ≤ U → R' (critNum M ys x) - R' (critNum M ys (x-1))
      ≤ R' (critNum M ys (x+1)) - R' (critNum M ys x) := by
  have hmonoR := conv_mono_above hRc hglob hysU
  have hantiR := conv_anti_below hRc hglob hysU
  have hb := M.b_pos
  have hh : ∀ t, ys ≤ t → critNum M ys t = t := fun t ht =>
    max_eq_left (le_trans (min_le_left _ _) ht)
  have hh2 : ∀ t, t ≤ ys → critNum M ys t = min ys (t + M.b) := by
    intro t ht
    unfold critNum
    apply max_eq_right
    rcases le_total ys (t + M.b) with h | h
    · rw [min_eq_left h]; exact ht
    · rw [min_eq_right h]; omega
  intro x hx
  have e1 : x - 1 + 1 = x := by ring
  by_cases hA : ys ≤ x - 1
  · rw [hh _ hA, hh x (by omega), hh (x+1) (by omega)]
    have := hRc x hx
    linarith
  · push_neg at hA
    by_cases hB : ys ≤ x
    · have hxy : x = ys := by omega
      have c1 : critNum M ys (x-1) = ys := by
        rw [hh2 _ (by omega)]; apply min_eq_left; omega
      rw [c1, hh x hB, hh (x+1) (by omega)]
      have := hmonoR x (x+1) hB (by omega) hx
      subst hxy
      linarith
    · push_neg at hB
      -- x < ys
      rw [hh2 (x-1) (by omega), hh2 x (by omega), hh2 (x+1) (by omega)]
      by_cases hC1 : x + 1 + M.b ≤ ys
      · rw [min_eq_right (show x - 1 + M.b ≤ ys by omega), min_eq_right (show x + M.b ≤ ys by omega),
          min_eq_right (show x + 1 + M.b ≤ ys by omega)]
        have := hRc (x + M.b) (by omega)
        have e2 : x - 1 + M.b = x + M.b - 1 := by ring
        rw [e2]
        have e3 : x + 1 + M.b = x + M.b + 1 := by ring
        rw [e3]
        linarith
      · push_neg at hC1
        by_cases hC2 : x + M.b ≤ ys
        · have hq : x + M.b = ys := by omega
          rw [min_eq_right (show x - 1 + M.b ≤ ys by omega), min_eq_left (show ys ≤ x + M.b by omega),
            min_eq_left (show ys ≤ x + 1 + M.b by omega)]
          have := hantiR (ys - 1) ys (by omega) le_rfl
          have e4 : x - 1 + M.b = ys - 1 := by omega
          rw [e4]
          linarith
        · push_neg at hC2
          rw [min_eq_left (show ys ≤ x - 1 + M.b by omega), min_eq_left (show ys ≤ x + M.b by omega),
            min_eq_left (show ys ≤ x + 1 + M.b by omega)]
          try linarith


lemma pow_add_le2 (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (n : ℕ) :
    (a + c) ^ n ≤ 2 ^ n * (a ^ n + c ^ n) := by
  have h2 : a + c ≤ 2 * max a c := by
    have := le_max_left a c
    have := le_max_right a c
    linarith
  have h3 : (a + c) ^ n ≤ (2 * max a c) ^ n := pow_le_pow_left₀ (by positivity) h2 n
  have h4 : (max a c) ^ n ≤ a ^ n + c ^ n := by
    rcases le_total a c with h | h
    · rw [max_eq_right h]; have : 0 ≤ a ^ n := by positivity
      linarith
    · rw [max_eq_left h]; have : 0 ≤ c ^ n := by positivity
      linarith
  calc (a + c) ^ n ≤ (2 * max a c) ^ n := h3
    _ = 2 ^ n * (max a c) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (a ^ n + c ^ n) := mul_le_mul_of_nonneg_left h4 (by positivity)

lemma poly_series_bound (M : Model) (n : ℕ) (A B : ℝ) (U : ℤ) (v : ℤ → ℝ)
    (hv : ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ n) :
    ∃ A' B' : ℝ, ∀ y ≤ U, |∑' j : ℕ, M.p j * v (y - j)| ≤ A' + B' * |(y:ℝ)| ^ n := by
  have hp := M.p_nonneg
  have hn := moments_finite M n
  have hs := M.p_sum
  refine ⟨|A| + |B| * 2 ^ n * (∑' j : ℕ, M.p j * (j:ℝ)^n), |B| * 2 ^ n, fun y hy => ?_⟩
  have hsum : HasSum (fun j : ℕ => M.p j * |A| + |B| * 2 ^ n * (|(y:ℝ)| ^ n * M.p j + M.p j * (j:ℝ) ^ n))
      (1 * |A| + |B| * 2 ^ n * (|(y:ℝ)| ^ n * 1 + ∑' j : ℕ, M.p j * (j:ℝ)^n)) :=
    (hs.mul_right _).add (((hs.mul_left (|(y:ℝ)| ^ n)).add hn.hasSum).mul_left _)
  have key := tsum_of_norm_bounded hsum (f := fun j : ℕ => M.p j * v (y - j)) (fun j => ?_)
  · rw [Real.norm_eq_abs] at key
    calc _ ≤ _ := key
      _ = _ := by ring
  · have hyj : y - (j:ℤ) ≤ U := by omega
    have h1 := hv (y - j) hyj
    have h2 := abs_sub_pow_le (y:ℝ) j n
    have hc : ((y - (j:ℤ) : ℤ) : ℝ) = (y:ℝ) - (j:ℝ) := by push_cast; ring
    rw [hc] at h1
    have h3 : |v (y - j)| ≤ |A| + |B| * (2 ^ n * (|(y:ℝ)| ^ n + (j:ℝ) ^ n)) := by
      calc |v (y - j)| ≤ A + B * |(y:ℝ) - (j:ℝ)| ^ n := h1
        _ ≤ |A| + |B| * |(y:ℝ) - (j:ℝ)| ^ n := by
            have := le_abs_self A
            have : B * |(y:ℝ) - (j:ℝ)| ^ n ≤ |B| * |(y:ℝ) - (j:ℝ)| ^ n :=
              mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
            linarith
        _ ≤ _ := by
            have := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
            linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp j)]
    calc M.p j * |v (y - j)| ≤ M.p j * (|A| + |B| * (2 ^ n * (|(y:ℝ)| ^ n + (j:ℝ) ^ n))) :=
          mul_le_mul_of_nonneg_left h3 (hp j)
      _ = _ := by ring

lemma R_growth (M : Model) (U : ℤ) (v : ℤ → ℝ) (A B : ℝ)
    (hv : ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ (M.ρ + 3)) :
    ∃ A1 B1 : ℝ, ∀ y ≤ U, |R M v y| ≤ A1 + B1 * |(y:ℝ)| ^ (M.ρ + 3) := by
  obtain ⟨AG, BG, hAG, hBG, hG⟩ := M.G_growth
  obtain ⟨A', B', hAB⟩ := poly_series_bound M (M.ρ + 3) A B U v hv
  refine ⟨AG + BG + A', BG + B', fun y hy => ?_⟩
  have h1 := hAB y hy
  have h2 := hG y
  have h3 := M.G_nonneg y
  have h4 : |(y:ℝ)| ^ M.ρ ≤ 1 + |(y:ℝ)| ^ (M.ρ + 3) := by
    rcases le_total |(y:ℝ)| 1 with h | h
    · have := pow_le_one₀ (abs_nonneg (y:ℝ)) h (n := M.ρ)
      have : 0 ≤ |(y:ℝ)| ^ (M.ρ + 3) := by positivity
      linarith
    · have := pow_le_pow_right₀ h (show M.ρ ≤ M.ρ + 3 by omega)
      linarith
  unfold R
  calc |M.G y + ∑' j : ℕ, M.p j * v (y - j)| ≤ |M.G y| + |∑' j : ℕ, M.p j * v (y - j)| := abs_add_le _ _
    _ ≤ (AG + BG * |(y:ℝ)| ^ M.ρ) + (A' + B' * |(y:ℝ)| ^ (M.ρ + 3)) := by
        rw [abs_of_nonneg h3]; linarith
    _ ≤ _ := by nlinarith

lemma InV_sub_const (M : Model) (U yInf : ℤ) (v : ℤ → ℝ) (hv : InV M U yInf v) (c : ℝ) :
    InV M U yInf (fun x => v x - c) := by
  obtain ⟨⟨A, B, hAB⟩, hm, hc⟩ := hv
  refine ⟨⟨A + |c|, B, fun x hx => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · have := hAB x hx
    have := abs_sub (v x) c
    linarith
  · have := hm x hx; simp only; linarith
  · have := hc x hx; simp only; linarith


lemma crit_eq_of_le (M : Model) (ys t : ℤ) (ht : t ≤ ys) :
    critNum M ys t = min ys (t + M.b) := by
  have hb := M.b_pos
  unfold critNum
  apply max_eq_right
  rcases le_total ys (t + M.b) with h | h
  · rw [min_eq_left h]; exact ht
  · rw [min_eq_right h]; omega

lemma S_inV (M : Model) (U yInf : ℤ) (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf)
    (hU : yInf ≤ U) (v : ℤ → ℝ) (hv : InV M U yInf v)
    (hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) :
    ∃ ys : ℤ, yInf ≤ ys ∧ ys ≤ U ∧ (∀ z ≤ U, R M v ys ≤ R M v z) ∧ InV M U yInf (S M U v) := by
  obtain ⟨ys, hys1, hys2, hglob⟩ := R_min_exists M U yInf hyInf hU v hv hsum
  have hRc := R_convex M U v hv.2.2 hsum
  have hantiR := conv_anti_below hRc hglob hys2
  refine ⟨ys, hys1, hys2, hglob, ?_, ?_, ?_⟩
  · obtain ⟨A, B, hAB⟩ := hv.1
    obtain ⟨A1, B1, h1⟩ := R_growth M U v A B hAB
    refine ⟨A1 + |B1| * 2 ^ (M.ρ + 3) * (M.b:ℝ) ^ (M.ρ + 3), |B1| * 2 ^ (M.ρ + 3), fun x hx => ?_⟩
    rw [S_eq_R M U v hRc hys2 hglob x hx]
    obtain ⟨⟨c1, c2, c3⟩, _⟩ := crit_opt M U (R M v) hRc hys2 hglob x hx
    have h1y := h1 _ c3
    have hy : |((critNum M ys x : ℤ) : ℝ)| ≤ |(x:ℝ)| + (M.b:ℝ) := by
      have a1 : (x:ℝ) ≤ ((critNum M ys x : ℤ) : ℝ) := by exact_mod_cast c1
      have a2 : ((critNum M ys x : ℤ) : ℝ) ≤ (x:ℝ) + (M.b:ℝ) := by exact_mod_cast c2
      apply abs_le.2
      constructor
      · linarith [neg_abs_le (x:ℝ), (Nat.cast_nonneg M.b : (0:ℝ) ≤ M.b)]
      · linarith [le_abs_self (x:ℝ)]
    have hy2 : |((critNum M ys x : ℤ) : ℝ)| ^ (M.ρ + 3) ≤ 2 ^ (M.ρ + 3) * (|(x:ℝ)| ^ (M.ρ + 3) + (M.b:ℝ) ^ (M.ρ + 3)) :=
      (pow_le_pow_left₀ (abs_nonneg _) hy _).trans (pow_add_le2 _ _ (abs_nonneg _) (Nat.cast_nonneg _) _)
    have hB : B1 * |((critNum M ys x : ℤ) : ℝ)| ^ (M.ρ + 3) ≤
        |B1| * (2 ^ (M.ρ + 3) * (|(x:ℝ)| ^ (M.ρ + 3) + (M.b:ℝ) ^ (M.ρ + 3))) :=
      (mul_le_mul_of_nonneg_right (le_abs_self B1) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hy2 (abs_nonneg _))
    calc _ ≤ A1 + B1 * |((critNum M ys x : ℤ) : ℝ)| ^ (M.ρ + 3) := h1y
      _ ≤ _ := by nlinarith
  · intro x hx
    have hxU : x ≤ U := by omega
    have hx1U : x + 1 ≤ U := by omega
    rw [S_eq_R M U v hRc hys2 hglob (x+1) hx1U, S_eq_R M U v hRc hys2 hglob x hxU,
      crit_eq_of_le M ys x (by omega), crit_eq_of_le M ys (x+1) (by omega)]
    have hb := M.b_pos
    exact hantiR _ _ (min_le_min le_rfl (by omega)) (min_le_left _ _)
  · intro x hx
    have := g_convex M U (R M v) hRc hys2 hglob x hx
    rw [S_eq_R M U v hRc hys2 hglob (x-1) (by omega), S_eq_R M U v hRc hys2 hglob x (by omega),
      S_eq_R M U v hRc hys2 hglob (x+1) hx]
    exact this

theorem lemma5_full (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U)
    (v : ℤ → ℝ) (hv : InV M U yInf v) :
    (∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) ∧
    InV M U yInf (S M U v) ∧ InV M U yInf (Q M U yInf v) ∧
    ∀ L : ℤ, L ≤ yInf - M.b →
      (∀ x ≤ U, SL M U L v x = S M U v x) ∧ (∀ x ≤ U, QL M U L yInf v x = Q M U yInf v x) := by
  have hsum : ∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j)) := by
    obtain ⟨⟨A, B, hAB⟩, _, _⟩ := hv
    exact fun y hy => summable_poly M (M.ρ + 3) A B U v hAB y hy
  obtain ⟨ys, hys1, hys2, hglob, hS⟩ := S_inV M U yInf hyInf hU v hv hsum
  have hRc := R_convex M U v hv.2.2 hsum
  refine ⟨hsum, hS, InV_sub_const M U yInf (S M U v) hS (S M U v yInf), ?_⟩
  intro L hL
  have hb := M.b_pos
  have hSL : ∀ x ≤ U, SL M U L v x = S M U v x := by
    intro x hx
    unfold SL
    split_ifs with h
    · rw [S_eq_R M U v hRc hys2 hglob x hx]
      have : critNum M ys x = x + M.b := by
        unfold critNum
        rw [min_eq_right (by omega)]
        exact max_eq_right (by omega)
      rw [this]
    · rfl
  refine ⟨hSL, fun x hx => ?_⟩
  unfold QL Q
  rw [hSL x hx, hSL yInf hU]

end FZ9

open FedergruenZipkin.AvgCost in
theorem solution (M : Model) (U yInf : ℤ)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U)
    (v : ℤ → ℝ) (hv : InV M U yInf v) :
    (∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) ∧
    InV M U yInf (S M U v) ∧ InV M U yInf (Q M U yInf v) ∧
    ∀ L : ℤ, L ≤ yInf - M.b →
      (∀ x ≤ U, SL M U L v x = S M U v x) ∧ (∀ x ≤ U, QL M U L yInf v x = Q M U yInf v x) := by
  exact FZ9.lemma5_full M U yInf hyInf hU v hv
