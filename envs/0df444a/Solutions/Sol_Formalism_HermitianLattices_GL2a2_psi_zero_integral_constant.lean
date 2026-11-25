-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2a2.psi_zero_integral_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:07.033984+00:00
-- url     : https://prove2.me/submissions/71ef7c46-9bc5-41bf-a5da-a5d3aa08f6ef

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PsiZeroIntegral
import Theorems.Thm_Formalism_ZeroFreeDirichlet_siegelWalfisz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Filter Topology ArithmeticFunction MeasureTheory
noncomputable section
namespace Formalism.HermitianLattices.P.PsiZeroIntegral
private lemma dom_integrableOn {a : ℝ} (ha : 1 < a) : IntegrableOn dom (Set.Ioi a) := by
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (g := fun t : ℝ => -(Real.log t)⁻¹) (l := 0) ?_ ?_ ?_ ?_
  · exact (((Real.continuousAt_log (by linarith)).inv₀ (Real.log_pos ha).ne').neg).continuousWithinAt
  · intro x hx
    have hx1 : (1 : ℝ) < x := lt_trans ha hx
    have hx0 : x ≠ 0 := (by linarith : (0 : ℝ) < x).ne'
    have hl : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    have h := ((Real.hasDerivAt_log hx0).inv hl).neg
    refine h.congr_deriv ?_
    unfold dom
    first
      | (rw [neg_div, neg_neg, one_div, mul_inv, div_eq_mul_inv])
      | (field_simp; done)
      | (field_simp; ring)
  · intro x hx
    have hx1 : (1 : ℝ) < x := lt_trans ha hx
    unfold dom
    have hpos : 0 < x * Real.log x ^ 2 := mul_pos (by linarith) (pow_pos (Real.log_pos hx1) 2)
    exact (one_div_pos.2 hpos).le
  · have h := (Real.tendsto_log_atTop.inv_tendsto_atTop).neg
    simpa using h
private lemma exp_sqrt_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / c ^ 4 / Real.log x ^ 2 := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hy0 : 0 < c * Real.sqrt (Real.log x) := mul_pos hc (Real.sqrt_pos.2 hL)
  have h4 : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    rw [mul_pow, show Real.sqrt (Real.log x) ^ 4 = (Real.sqrt (Real.log x) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hL.le]
  have hexp : (c * Real.sqrt (Real.log x)) ^ 4 / 24 ≤ Real.exp (c * Real.sqrt (Real.log x)) := by
    have h := Real.pow_div_factorial_le_exp _ hy0.le 4
    norm_num [Nat.factorial] at h
    linarith
  rw [show -c * Real.sqrt (Real.log x) = -(c * Real.sqrt (Real.log x)) by ring, Real.exp_neg,
    div_div, ← h4]
  have hq : 0 < (c * Real.sqrt (Real.log x)) ^ 4 / 24 := by positivity
  calc (Real.exp (c * Real.sqrt (Real.log x)))⁻¹
      = 1 / Real.exp (c * Real.sqrt (Real.log x)) := inv_eq_one_div _
    _ ≤ 1 / ((c * Real.sqrt (Real.log x)) ^ 4 / 24) := one_div_le_one_div_of_le hq hexp
    _ = 24 / (c * Real.sqrt (Real.log x)) ^ 4 := by field_simp
private lemma norm_cpow_neg_add_one {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    ‖(t : ℂ) ^ (-((σ : ℂ) + 1))‖ = t ^ (-(σ + 1)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  congr 1
private lemma rem_measurable (a : ℕ → ℂ) (m : ℂ) : Measurable (rem a m) := by
  unfold rem
  exact ((measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 1 n, a k)).comp Nat.measurable_floor).sub
    (measurable_const.mul Complex.measurable_ofReal)
private lemma F_measurable (a : ℕ → ℂ) (m : ℂ) (s : ℂ) :
    Measurable (fun t : ℝ => rem a m t * (t : ℂ) ^ s) := by
  exact (rem_measurable a m).mul (Complex.measurable_ofReal.pow_const s)
private lemma core_integrable {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) :
    IntegrableOn (fun t : ℝ => rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))) (Set.Ioi 1) := by
  obtain ⟨K, x₁, hx₁, hK⟩ := h
  rw [← Set.Ioc_union_Ioi_eq_Ioi hx₁.le]
  refine IntegrableOn.union ?_ ?_
  · refine MeasureTheory.Integrable.mono'
      ((continuous_const (y := ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁)).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self)
      (F_measurable a m _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht.1
    rw [norm_mul, norm_cpow_neg_add_one ht0 1]
    have hp : t ^ (-((1 : ℝ) + 1)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht.1.le (by norm_num)
    have hr : ‖rem a m t‖ ≤ ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁ := by
      unfold rem
      calc ‖(∑ k ∈ Icc 1 ⌊t⌋₊, a k) - m * t‖ ≤ ‖∑ k ∈ Icc 1 ⌊t⌋₊, a k‖ + ‖m * (t : ℂ)‖ := norm_sub_le _ _
        _ ≤ ∑ k ∈ Icc 1 ⌊t⌋₊, ‖a k‖ + ‖m‖ * x₁ := by
            refine add_le_add (norm_sum_le _ _) ?_
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
            exact mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)
        _ ≤ ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁ := by
            refine add_le_add ?_ le_rfl
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono ht.2)
            · intro i _ _
              exact norm_nonneg _
    calc ‖rem a m t‖ * t ^ (-((1 : ℝ) + 1)) ≤ (∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁) * 1 :=
          mul_le_mul hr hp (Real.rpow_nonneg ht0.le _) (le_trans (norm_nonneg _) hr)
      _ = ∑ k ∈ Icc 1 ⌊x₁⌋₊, ‖a k‖ + ‖m‖ * x₁ := mul_one _
  · refine MeasureTheory.Integrable.mono' (MeasureTheory.Integrable.const_mul (dom_integrableOn hx₁) K)
      (F_measurable a m _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : x₁ ≤ t := le_of_lt ht
    have ht0 : 0 < t := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [norm_mul, norm_cpow_neg_add_one ht0 1]
    have h2 : t ^ (-((1 : ℝ) + 1)) = (t ^ 2)⁻¹ := by
      rw [show -((1 : ℝ) + 1) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    rw [h2]
    calc ‖rem a m t‖ * (t ^ 2)⁻¹ ≤ K * t / Real.log t ^ 2 * (t ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (hK t ht') (by positivity)
      _ = K * dom t := by
          unfold dom
          field_simp
private lemma F_bound (a : ℕ → ℂ) (m : ℂ) {σ : ℝ} (hσ : 1 ≤ σ) {t : ℝ} (ht : 1 < t) :
    ‖rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1))‖ ≤ ‖rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))‖ := by
  have ht0 : 0 < t := by linarith
  rw [norm_mul, norm_mul, norm_cpow_neg_add_one ht0 σ, norm_cpow_neg_add_one ht0 1]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (norm_nonneg _)
private lemma core_integrable' {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) {σ : ℝ} (hσ : 1 ≤ σ) :
    IntegrableOn (fun t : ℝ => rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1))) (Set.Ioi 1) := by
  refine MeasureTheory.Integrable.mono (core_integrable h) ((F_measurable a m _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact F_bound a m hσ ht
private lemma core_tendsto {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) :
    Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] 1) (𝓝 (∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)))) := by
  have hI : Tendsto (fun σ : ℝ => ∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] 1) (𝓝 (∫ t in Set.Ioi (1 : ℝ), rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => ‖rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))‖) ?_ ?_ (core_integrable h).norm ?_
    · exact Eventually.of_forall fun σ => (F_measurable a m _).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => F_bound a m (le_of_lt hσ) ht
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : (t : ℂ) ≠ 0 := by
        have : (0 : ℝ) < t := lt_trans zero_lt_one ht
        exact_mod_cast this.ne'
      have hc : Continuous (fun σ : ℝ => rem a m t * (t : ℂ) ^ (-((σ : ℂ) + 1))) :=
        continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl ht0))
      exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hσ : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  simpa using hσ.mul hI
private lemma sum_eq_rem (a : ℕ → ℂ) (m : ℂ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, a k = rem a m n + m * n := by
  simp only [rem, Nat.floor_natCast, Complex.ofReal_natCast]
  ring
private lemma rem_bigO {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  obtain ⟨K, x₁, hx₁, hK⟩ := h
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hx : ∀ᶠ n : ℕ in atTop, x₁ ≤ n := tendsto_natCast_atTop_atTop.eventually_ge_atTop x₁
  refine Asymptotics.IsBigO.of_bound (|K| + ‖m‖) ?_
  filter_upwards [hlog, hx] with n hl hxn
  rw [sum_eq_rem a m n]
  have h1 := hK n hxn
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [Real.rpow_one, Real.norm_of_nonneg hn0]
  have hL : 1 ≤ Real.log n ^ 2 := by nlinarith
  have h2 : ‖rem a m n‖ ≤ |K| * n := by
    calc ‖rem a m n‖ ≤ K * n / Real.log n ^ 2 := h1
      _ ≤ |K| * n / Real.log n ^ 2 := by gcongr; exact le_abs_self K
      _ ≤ |K| * n := div_le_self (by positivity) hL
  have h3 : ‖m * (n : ℂ)‖ = ‖m‖ * n := by
    rw [norm_mul]
    simp
  calc ‖rem a m n + m * n‖ ≤ ‖rem a m n‖ + ‖m * (n : ℂ)‖ := norm_add_le _ _
    _ ≤ |K| * n + ‖m‖ * n := by rw [h3]; linarith
    _ = (|K| + ‖m‖) * n := by ring
private lemma ofReal_tendsto_punctured :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (Complex.continuous_ofReal.tendsto' (1 : ℝ) 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [Set.mem_compl_singleton_iff]
    have h1 : σ ≠ 1 := (show (1 : ℝ) < σ from hσ).ne'
    exact_mod_cast h1
private lemma zeta_logderiv_limit :
    Tendsto (fun s : ℂ => deriv riemannZeta s / riemannZeta s + 1 / (s - 1)) (𝓝[≠] 1)
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = Function.update (fun s => (s - 1) * riemannZeta s) 1 1 := ⟨_, rfl⟩
  have hgs : ∀ s : ℂ, s ≠ 1 → g s = (s - 1) * riemannZeta s := fun s hs => by
    simp [hg, Function.update_apply, hs]
  have h1 : g 1 = 1 := by simp [hg]
  have hdiff : Differentiable ℂ g := by
    have hon : DifferentiableOn ℂ g (Set.univ \ {1}) := by
      intro s hs
      have hs1 : s ≠ 1 := hs.2
      have hev : g =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
        exact hgs z hz
      exact (((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)).congr_of_eventuallyEq
        hev).differentiableWithinAt
    have hcont : ContinuousAt g 1 := by
      rw [continuousAt_iff_punctured_nhds, h1]
      refine riemannZeta_residue_one.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hgs s hs).symm
    have hall := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff Filter.univ_mem).1 ⟨hon, hcont⟩
    exact differentiableOn_univ.1 hall
  have hd1 : deriv g 1 = Real.eulerMascheroniConstant := by
    have h2 := hasDerivAt_iff_tendsto_slope.1 (hdiff 1).hasDerivAt
    have h3 : Tendsto (slope g 1) (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
      refine tendsto_riemannZeta_sub_one_div.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
      rw [slope_def_field, hgs s hs, h1]
      first
        | (field_simp; done)
        | (field_simp; ring)
    exact tendsto_nhds_unique h2 h3
  have hcd : ContinuousAt (deriv g) 1 := ((hdiff.analyticAt 1).deriv).continuousAt
  have hlim : Tendsto (fun s => deriv g s / g s) (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    have h4 : Tendsto (fun s => deriv g s / g s) (𝓝[≠] 1) (𝓝 (deriv g 1 / g 1)) :=
      (hcd.div (hdiff 1).continuousAt (by rw [h1]; exact one_ne_zero)).tendsto.mono_left
        nhdsWithin_le_nhds
    rw [hd1, h1, div_one] at h4
    exact h4
  refine hlim.congr' ?_
  have hne : ∀ᶠ s in 𝓝[≠] (1 : ℂ), g s ≠ 0 :=
    ((hdiff 1).continuousAt.eventually_ne (by rw [h1]; exact one_ne_zero)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hne] with s hs hgs0
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have hev : g =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
    exact hgs z hz
  have hdg : deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [hev.deriv_eq]
    have h5 : HasDerivAt (fun z => (z - 1) * riemannZeta z)
        (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
      ((hasDerivAt_id' s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
    rw [h5.deriv]
    ring
  rw [hgs s hs] at hgs0 ⊢
  have hz : riemannZeta s ≠ 0 := right_ne_zero_of_mul hgs0
  rw [hdg]
  first
    | (field_simp; done)
    | (field_simp; ring)
private lemma sw_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    RemBound (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) (if χ = 1 then 1 else 0) := by
  obtain ⟨c, C, hc, h⟩ := Formalism.ZeroFreeDirichlet.siegelWalfisz 1 one_pos
  have hE : 0 < Real.exp (q : ℝ) := Real.exp_pos _
  refine ⟨|C| * (24 / c ^ 4), Real.exp q + 2, by linarith, fun t ht => ?_⟩
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hq : (q : ℝ) ≤ Real.log t ^ (1 : ℝ) := by
    rw [Real.rpow_one, Real.le_log_iff_exp_le ht0]
    linarith
  have h1 := h q χ t ht2 hq
  have e : rem (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) (if χ = 1 then 1 else 0) t =
      Formalism.ZeroFreeDirichlet.psiChi χ t - (if χ = 1 then (t : ℂ) else 0) := by
    unfold rem Formalism.ZeroFreeDirichlet.psiChi
    split_ifs <;> simp
  rw [e]
  refine h1.trans ?_
  have h2 := exp_sqrt_le hc (x := t) (by linarith)
  calc C * t * Real.exp (-c * Real.sqrt (Real.log t))
      ≤ |C| * t * (24 / c ^ 4 / Real.log t ^ 2) := by
        gcongr
        exact le_abs_self C
    _ = |C| * (24 / c ^ 4) * t / Real.log t ^ 2 := by ring
private theorem psiZeroConst_main : Formalism.HermitianLattices.GL2a2.PsiZeroConst := by
  unfold Formalism.HermitianLattices.GL2a2.PsiZeroConst
  have hsub : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
  have hone : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := fun n => by
    first
      | exact MulChar.one_apply (isUnit_of_subsingleton _)
      | simp
  have h : RemBound (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 := by
    have h0 := sw_bound 1 (1 : DirichletCharacter ℂ 1)
    rw [if_pos rfl] at h0
    simp only [hone, mul_one] at h0
    exact h0
  have hid : ∀ σ : ℝ, 1 < σ →
      (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1))
        = -(deriv riemannZeta σ / riemannZeta σ + 1 / ((σ : ℂ) - 1)) - 1 := by
    intro σ hσ
    have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
    have hne : (σ : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hσ.ne'
    have hne' : -(σ : ℂ) + 1 ≠ 0 := by
      intro h0
      apply hne
      linear_combination -h0
    have hsum : LSeriesSummable (fun n : ℕ => ((Λ n : ℝ) : ℂ)) σ := by
      first
        | exact ArithmeticFunction.LSeriesSummable_vonMangoldt hre
        | exact LSeriesSummable_vonMangoldt hre
    have hL := LSeries_eq_mul_integral (fun n : ℕ => ((Λ n : ℝ) : ℂ)) zero_le_one hre hsum (rem_bigO h)
    have key : LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ)) σ = -deriv riemannZeta σ / riemannZeta σ :=
      LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
    have hpint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(σ : ℂ))) (Set.Ioi 1) :=
      integrableOn_Ioi_cpow_of_lt (by simpa using hσ) one_pos
    have hsplit : ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) * (t : ℂ) ^ (-((σ : ℂ) + 1))
        = (∫ t in Set.Ioi (1 : ℝ), rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
          + ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-(σ : ℂ)) := by
      rw [← integral_add (core_integrable' h hσ.le) hpint]
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (t : ℂ) ≠ 0 := by
        exact_mod_cast (show (0 : ℝ) < t from lt_trans one_pos ht).ne'
      simp only [rem]
      rw [show -(σ : ℂ) = 1 + (-((σ : ℂ) + 1)) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]
      ring
    have hpow : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-(σ : ℂ)) = 1 / ((σ : ℂ) - 1) := by
      rw [integral_Ioi_cpow_of_lt (by simpa using hσ) one_pos, Complex.ofReal_one, Complex.one_cpow,
        div_eq_div_iff hne' hne]
      ring
    have hq : (σ : ℂ) * (1 / ((σ : ℂ) - 1)) = 1 / ((σ : ℂ) - 1) + 1 := by
      rw [mul_one_div, div_add_one hne]
      congr 1
      ring
    have hmain : (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
        rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1))
        = LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ)) σ - (σ : ℂ) * (1 / ((σ : ℂ) - 1)) := by
      rw [hL, hsplit, hpow]
      ring
    rw [hmain, key, hq]
    ring
  have hG : Tendsto (fun σ : ℝ => -(deriv riemannZeta σ / riemannZeta σ + 1 / ((σ : ℂ) - 1)) - 1)
      (𝓝[>] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - 1)) :=
    ((zeta_logderiv_limit.comp ofReal_tendsto_punctured).neg).sub_const 1
  have hF : Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
      rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 t * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (𝓝[>] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - 1)) := by
    refine hG.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hid σ hσ).symm
  have hlim := tendsto_nhds_unique (core_tendsto h) hF
  have hF1 : ∀ u ∈ Set.Ioi (1 : ℝ),
      rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 u * (u : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))
        = (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ) := by
    intro u hu
    rw [show -(((1 : ℝ) : ℂ) + 1) = -((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]
    simp only [rem, Formalism.HermitianLattices.GL2PrimeSums.psumR]
    push_cast
    ring
  have hint : IntegrableOn (fun u : ℝ => (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2)
      (Set.Ioi 1) := by
    refine (MeasureTheory.Integrable.re (core_integrable h)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [hF1 u hu, RCLike.re_to_complex, Complex.ofReal_re]
  have e1 : ∫ u in Set.Ioi (1 : ℝ), (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ)
      = ∫ u in Set.Ioi (1 : ℝ),
        rem (fun n : ℕ => ((Λ n : ℝ) : ℂ)) 1 u * (u : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)) :=
    (setIntegral_congr_fun measurableSet_Ioi hF1).symm
  have hval : ∫ u in Set.Ioi (1 : ℝ), (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2
      = -1 - Real.eulerMascheroniConstant := by
    apply Complex.ofReal_injective
    have e0 : ∫ u in Set.Ioi (1 : ℝ), (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ)
        = ((∫ u in Set.Ioi (1 : ℝ), (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ) := by
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [← e0, e1, hlim]
    push_cast
    ring
  have hT := intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id
  rw [hval] at hT
  exact hT
end Formalism.HermitianLattices.P.PsiZeroIntegral
namespace Formalism.HermitianLattices.GL2a2
end Formalism.HermitianLattices.GL2a2
end
end

set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2a2
namespace Formalism.HermitianLattices.GL2a2
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.PsiZeroConst := by
  exact Formalism.HermitianLattices.P.PsiZeroIntegral.psiZeroConst_main
end Formalism.HermitianLattices.GL2a2
