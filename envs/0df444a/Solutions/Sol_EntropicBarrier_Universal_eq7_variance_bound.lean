-- Prove2me | solution 1 for EntropicBarrier.Universal.eq7_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T23:19:24.435707+00:00
-- url     : https://prove2.me/submissions/01ce6ab8-276c-4eac-8774-22ce8c9d7f2d

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily
import Theorems.Thm_ConvexOptimization_prekopa_leindler

set_option autoImplicit false

open scoped RealInnerProductSpace ENNReal Pointwise
open MeasureTheory Filter Topology Metric

namespace EB7

open EntropicBarrier.Universal

/-! ## Parametric integrals over a compact set, one real parameter -/

theorem cont_slice1 {n : ℕ} (G : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : Continuous (Function.uncurry G)) (s : ℝ) : Continuous (G s) :=
  hG.comp (continuous_const.prodMk continuous_id)

theorem hasDerivAt_setIntegral1 {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (G G' : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : Continuous (Function.uncurry G)) (hG' : Continuous (Function.uncurry G'))
    (hd : ∀ s x, HasDerivAt (G · x) (G' s x) s) (s0 : ℝ) :
    HasDerivAt (fun s => ∫ x in K, G s x) (∫ x in K, G' s0 x) s0 := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s0 1).prod hK).bddAbove_image hG'.norm.continuousOn
  have hfin : volume K < ⊤ := hK.measure_lt_top
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (ball_mem_nhds s0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s => (cont_slice1 G hG s).aestronglyMeasurable
  · exact (cont_slice1 G hG s0).continuousOn.integrableOn_compact hK
  · exact (cont_slice1 G' hG' s0).aestronglyMeasurable
  · refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx s hs => ?_)
    exact hC (Set.mem_image_of_mem _ (Set.mk_mem_prod (ball_subset_closedBall hs) hx))
  · exact integrable_const C
  · exact Eventually.of_forall fun x s _ => hd s x

/-! ## The scaled partition function `F s = ∫_K exp (s ⟪θ, x⟫)` and its derivatives -/

noncomputable def F0 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) (s : ℝ) : ℝ :=
  ∫ x in K, Real.exp (s * ⟪θ, x⟫)

noncomputable def F1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) (s : ℝ) : ℝ :=
  ∫ x in K, ⟪θ, x⟫ * Real.exp (s * ⟪θ, x⟫)

noncomputable def F2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) (s : ℝ) : ℝ :=
  ∫ x in K, ⟪θ, x⟫ ^ 2 * Real.exp (s * ⟪θ, x⟫)

theorem hasDerivAt_F0 {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (θ : EuclideanSpace ℝ (Fin n)) (s : ℝ) : HasDerivAt (F0 K θ) (F1 K θ s) s := by
  refine hasDerivAt_setIntegral1 hK (fun s x => Real.exp (s * ⟪θ, x⟫))
    (fun s x => ⟪θ, x⟫ * Real.exp (s * ⟪θ, x⟫)) ?_ ?_ ?_ s
  · unfold Function.uncurry; fun_prop
  · unfold Function.uncurry; fun_prop
  · intro s x
    have h := ((hasDerivAt_id' s).mul_const (⟪θ, x⟫)).exp
    exact h.congr_deriv (by ring)

theorem hasDerivAt_F1 {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (θ : EuclideanSpace ℝ (Fin n)) (s : ℝ) : HasDerivAt (F1 K θ) (F2 K θ s) s := by
  refine hasDerivAt_setIntegral1 hK (fun s x => ⟪θ, x⟫ * Real.exp (s * ⟪θ, x⟫))
    (fun s x => ⟪θ, x⟫ ^ 2 * Real.exp (s * ⟪θ, x⟫)) ?_ ?_ ?_ s
  · unfold Function.uncurry; fun_prop
  · unfold Function.uncurry; fun_prop
  · intro s x
    have h := (((hasDerivAt_id' s).mul_const (⟪θ, x⟫)).exp).const_mul (⟪θ, x⟫)
    exact h.congr_deriv (by ring)

theorem volume_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    0 < volume K :=
  (isOpen_interior.measure_pos volume hK.2.2).trans_le (measure_mono interior_subset)

theorem F0_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) (s : ℝ) : 0 < F0 K θ s := by
  unfold F0
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (s * ⟪θ, x⟫)) := by
    fun_prop
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    (hc.continuousOn.integrableOn_compact hK.1)]
  have : Function.support (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (s * ⟪θ, x⟫)) =
      Set.univ := by
    ext x; simp [(Real.exp_pos _).ne']
  rw [this, Measure.restrict_apply_univ]
  exact volume_pos hK

/-! ## Change of variables and the Prékopa–Leindler step -/

theorem isCompact_smul {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (t : ℝ) : IsCompact (t • K) := by
  rw [← Set.image_smul]; exact hK.image (continuous_const_smul t)

theorem integral_smul_set {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    ∫ z in s • K, Real.exp ⟪θ, z⟫ = s ^ n * F0 K θ s := by
  have h := Measure.setIntegral_comp_smul_of_pos volume
    (fun z : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, z⟫) K hs
  simp only [inner_smul_right, finrank_euclideanSpace_fin, smul_eq_mul] at h
  unfold F0
  rw [h, ← mul_assoc, mul_inv_cancel₀ (pow_pos hs n).ne', one_mul]

noncomputable def hInd {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
  (t • K).indicator (fun z => ENNReal.ofReal (Real.exp ⟪θ, z⟫))

theorem measurable_hInd {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (θ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Measurable (hInd K θ t) := by
  unfold hInd
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, z⟫) := by fun_prop
  exact hc.measurable.ennreal_ofReal.indicator (isCompact_smul hK t).measurableSet

theorem lintegral_hInd {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (θ : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    ∫⁻ z, hInd K θ t z = ENNReal.ofReal (t ^ n * F0 K θ t) := by
  unfold hInd
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, z⟫) := by fun_prop
  rw [lintegral_indicator (isCompact_smul hK t).measurableSet, ← integral_smul_set K θ ht,
    ofReal_integral_eq_lintegral_ofReal
      (hc.continuousOn.integrableOn_compact (isCompact_smul hK t))
      (Eventually.of_forall fun z => (Real.exp_pos _).le)]

theorem pl_hyp {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) {s₀ s₁ l : ℝ} (h0 : 0 < s₀) (h1 : 0 < s₁)
    (hl0 : 0 < l) (hl1 : l < 1) (x y : EuclideanSpace ℝ (Fin n)) :
    hInd K θ s₀ x ^ (1 - l) * hInd K θ s₁ y ^ l ≤
      hInd K θ ((1 - l) * s₀ + l * s₁) ((1 - l) • x + l • y) := by
  unfold hInd
  by_cases hx : x ∈ s₀ • K
  · by_cases hy : y ∈ s₁ • K
    · have hs : 0 < (1 - l) * s₀ + l * s₁ := by nlinarith
      have hmem : (1 - l) • x + l • y ∈ ((1 - l) * s₀ + l * s₁) • K := by
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        set s := (1 - l) * s₀ + l * s₁
        have hcomb : ((1 - l) * s₀ / s) • a + (l * s₁ / s) • b ∈ K :=
          hK.2.1 ha hb (by positivity) (by positivity)
            (by rw [← add_div]; exact div_self hs.ne')
        have heq : (1 - l) • s₀ • a + l • s₁ • b =
            s • (((1 - l) * s₀ / s) • a + (l * s₁ / s) • b) := by
          rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
          congr 2 <;> field_simp
        rw [heq]
        exact Set.smul_mem_smul_set hcomb
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hmem,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by linarith),
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hl0.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _)]
      apply le_of_eq
      congr 1
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, inner_add_right, inner_smul_right,
        inner_smul_right]
      congr 1; ring
    · rw [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hl0, mul_zero]
      exact bot_le
  · rw [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos (by linarith), zero_mul]
    exact bot_le

theorem pl_scaled {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) {s₀ s₁ l : ℝ} (h0 : 0 < s₀) (h1 : 0 < s₁)
    (hl0 : 0 < l) (hl1 : l < 1) :
    (s₀ ^ n * F0 K θ s₀) ^ (1 - l) * (s₁ ^ n * F0 K θ s₁) ^ l ≤
      ((1 - l) * s₀ + l * s₁) ^ n * F0 K θ ((1 - l) * s₀ + l * s₁) := by
  have hs : 0 < (1 - l) * s₀ + l * s₁ := by nlinarith
  have hPL := ConvexOptimization.prekopa_leindler l hl0 hl1 (hInd K θ s₀) (hInd K θ s₁)
    (hInd K θ ((1 - l) * s₀ + l * s₁)) (measurable_hInd hK.1 θ _) (measurable_hInd hK.1 θ _)
    (measurable_hInd hK.1 θ _) (pl_hyp hK θ h0 h1 hl0 hl1)
  have hA : 0 ≤ s₀ ^ n * F0 K θ s₀ := (mul_pos (pow_pos h0 n) (F0_pos hK θ s₀)).le
  have hB : 0 ≤ s₁ ^ n * F0 K θ s₁ := (mul_pos (pow_pos h1 n) (F0_pos hK θ s₁)).le
  have hC : 0 ≤ ((1 - l) * s₀ + l * s₁) ^ n * F0 K θ ((1 - l) * s₀ + l * s₁) :=
    (mul_pos (pow_pos hs n) (F0_pos hK θ _)).le
  rw [lintegral_hInd hK.1 θ h0, lintegral_hInd hK.1 θ h1, lintegral_hInd hK.1 θ hs,
    ENNReal.ofReal_rpow_of_nonneg hA (by linarith), ENNReal.ofReal_rpow_of_nonneg hB hl0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hA _)] at hPL
  exact (ENNReal.ofReal_le_ofReal_iff hC).1 hPL

/-! ## `s ↦ n log s + log F s` is concave on `(0, ∞)` -/

noncomputable def Lf {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) (s : ℝ) : ℝ :=
  (n : ℝ) * Real.log s + Real.log (F0 K θ s)

theorem log_scaled {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    Real.log (s ^ n * F0 K θ s) = Lf K θ s := by
  unfold Lf
  rw [Real.log_mul (pow_pos hs n).ne' (F0_pos hK θ s).ne', Real.log_pow]

theorem concaveOn_Lf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : ConcaveOn ℝ (Set.Ioi 0) (Lf K θ) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst this; simp
  rcases hb.eq_or_lt with rfl | hb'
  · have : a = 1 := by linarith
    subst this; simp
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have hb1 : b < 1 := by linarith
  have ha1 : a = 1 - b := by linarith
  subst ha1
  have hP := pl_scaled hK θ hx' hy' hb' hb1
  have hA : 0 < x ^ n * F0 K θ x := mul_pos (pow_pos hx' n) (F0_pos hK θ x)
  have hB : 0 < y ^ n * F0 K θ y := mul_pos (pow_pos hy' n) (F0_pos hK θ y)
  have hs : 0 < (1 - b) * x + b * y := by nlinarith
  have hlog := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)) hP
  rw [Real.log_mul (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hB _).ne',
    Real.log_rpow hA, Real.log_rpow hB, log_scaled hK θ hx', log_scaled hK θ hy',
    log_scaled hK θ hs] at hlog
  exact hlog

/-! ## Second derivative at `s = 1` -/

theorem hasDerivAt_Lf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Lf K θ) ((n : ℝ) * s⁻¹ + F1 K θ s / F0 K θ s) s :=
  ((Real.hasDerivAt_log hs.ne').const_mul (n : ℝ)).add
    ((hasDerivAt_F0 hK.1 θ s).log (F0_pos hK θ s).ne')

theorem second_deriv_nonpos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) (θ : EuclideanSpace ℝ (Fin n)) :
    F2 K θ 1 / F0 K θ 1 - (F1 K θ 1 / F0 K θ 1) ^ 2 ≤ n := by
  set Ld : ℝ → ℝ := fun s => (n : ℝ) * s⁻¹ + F1 K θ s / F0 K θ s with hLd
  have hanti : AntitoneOn (deriv (Lf K θ)) (Set.Ioi 0) :=
    (concaveOn_Lf hK θ).antitoneOn_deriv fun x hx => (hasDerivAt_Lf hK θ hx).differentiableAt
  have hantiL : AntitoneOn Ld (Set.Ioi 0) := by
    intro a ha b hb hab
    have e1 := (hasDerivAt_Lf hK θ (show (0 : ℝ) < a from ha)).deriv
    have e2 := (hasDerivAt_Lf hK θ (show (0 : ℝ) < b from hb)).deriv
    have := hanti ha hb hab
    rw [e1, e2] at this
    exact this
  set G : ℝ → ℝ := fun s => Ld (max s (1 / 2)) with hG
  have hGanti : Antitone G := by
    intro a b hab
    exact hantiL (show (0 : ℝ) < max a (1 / 2) by positivity)
      (show (0 : ℝ) < max b (1 / 2) by positivity) (max_le_max hab le_rfl)
  have hdL : HasDerivAt Ld ((n : ℝ) * (-(1 ^ 2)⁻¹) +
      (F2 K θ 1 * F0 K θ 1 - F1 K θ 1 * F1 K θ 1) / F0 K θ 1 ^ 2) 1 :=
    ((hasDerivAt_inv one_ne_zero).const_mul (n : ℝ)).add
      ((hasDerivAt_F1 hK.1 θ 1).div (hasDerivAt_F0 hK.1 θ 1) (F0_pos hK θ 1).ne')
  have hdG : HasDerivAt G ((n : ℝ) * (-(1 ^ 2)⁻¹) +
      (F2 K θ 1 * F0 K θ 1 - F1 K θ 1 * F1 K θ 1) / F0 K θ 1 ^ 2) 1 := by
    refine hdL.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with s hs
    simp only [hG, max_eq_left hs.le]
  have hle := hdG.nonpos_of_antitone hGanti
  have hF := F0_pos hK θ 1
  have key : F2 K θ 1 / F0 K θ 1 - (F1 K θ 1 / F0 K θ 1) ^ 2 =
      (F2 K θ 1 * F0 K θ 1 - F1 K θ 1 * F1 K θ 1) / F0 K θ 1 ^ 2 := by
    field_simp
  rw [key]
  simp only [one_pow, inv_one, mul_neg, mul_one] at hle
  linarith

/-! ## Moments of the exponential family -/

theorem integral_expFamily' {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x, g x ∂(expFamily K θ) = (F0 K θ 1)⁻¹ * ∫ x in K, Real.exp ⟪θ, x⟫ * g x := by
  have hZ : logPartition K θ = Real.log (F0 K θ 1) := by
    unfold logPartition F0; simp only [one_mul]
  unfold expFamily
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top), ← integral_const_mul]
  congr 1; ext x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, Real.exp_sub, hZ,
    Real.exp_log (F0_pos hK θ 1)]
  ring

theorem isProb {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : IsProbabilityMeasure (expFamily K θ) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (⟪θ, x⟫ - logPartition K θ)) := by fun_prop
  have hfin : IsFiniteMeasure (expFamily K θ) := by
    unfold expFamily
    exact isFiniteMeasure_withDensity_ofReal
      (hc.continuousOn.integrableOn_compact hK.1).hasFiniteIntegral
  have h1 := integral_expFamily' hK θ (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h1
  have hF : F0 K θ 1 = ∫ x in K, Real.exp ⟪θ, x⟫ := by unfold F0; simp only [one_mul]
  rw [← hF, inv_mul_cancel₀ (F0_pos hK θ 1).ne'] at h1
  refine ⟨?_⟩
  rw [measureReal_def] at h1
  exact (ENNReal.toReal_eq_one_iff _).1 h1

theorem mean_phi {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ⟪θ, x⟫ ∂(expFamily K θ) = F1 K θ 1 / F0 K θ 1 := by
  rw [integral_expFamily' hK θ, div_eq_inv_mul]
  congr 1; unfold F1; congr 1; ext x; rw [one_mul, mul_comm]

theorem mean_phi_sq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ((fun x => ⟪θ, x⟫) ^ 2) x ∂(expFamily K θ) = F2 K θ 1 / F0 K θ 1 := by
  rw [integral_expFamily' hK θ, div_eq_inv_mul]
  congr 1; unfold F2; congr 1; ext x; rw [one_mul, mul_comm, Pi.pow_apply]

theorem memLp_phi {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : MemLp (fun x => ⟪θ, x⟫) 2 (expFamily K θ) := by
  have := isProb hK θ
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ⟪θ, x⟫) := by fun_prop
  obtain ⟨C, hC⟩ := hK.1.exists_bound_of_continuousOn hc.continuousOn
  have hae : ∀ᵐ x ∂(expFamily K θ), x ∈ K := by
    unfold expFamily
    exact Measure.AbsolutelyContinuous.ae_le (withDensity_absolutelyContinuous _ _)
      (ae_restrict_mem hK.1.measurableSet)
  exact MemLp.of_bound hc.aestronglyMeasurable C (hae.mono fun x hx => hC x hx)

theorem variance_phi_le {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    ProbabilityTheory.variance (fun x => ⟪θ, x⟫) (expFamily K θ) ≤ n := by
  have := isProb hK θ
  rw [ProbabilityTheory.variance_eq_sub (memLp_phi hK θ), mean_phi_sq hK θ, mean_phi hK θ]
  exact second_deriv_nonpos hK θ

end EB7

open EntropicBarrier.Universal in
theorem solution {n : ℕ} (hn : 80 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (θ : EuclideanSpace ℝ (Fin n)) (hθ : θ ≠ 0) :
    ProbabilityTheory.variance (fun x => ⟪‖θ‖⁻¹ • θ, x⟫) (expFamily K θ) ≤
      (n : ℝ) / ‖θ‖ ^ 2 * (1 + 100 * Real.sqrt (Real.log n / n)) := by
  have e : (fun x : EuclideanSpace ℝ (Fin n) => ⟪‖θ‖⁻¹ • θ, x⟫) =
      fun x => ‖θ‖⁻¹ * ⟪θ, x⟫ := by
    funext x; rw [real_inner_smul_left]
  rw [e, ProbabilityTheory.variance_const_mul]
  have hV := EB7.variance_phi_le hK θ
  have hθ2 : 0 < ‖θ‖ ^ 2 := by positivity
  have hε : 0 ≤ 100 * Real.sqrt (Real.log n / n) := by positivity
  calc (‖θ‖⁻¹) ^ 2 * ProbabilityTheory.variance (fun x => ⟪θ, x⟫) (expFamily K θ)
      ≤ (‖θ‖⁻¹) ^ 2 * n := mul_le_mul_of_nonneg_left hV (by positivity)
    _ = (n : ℝ) / ‖θ‖ ^ 2 * 1 := by rw [inv_pow, mul_one, div_eq_mul_inv, mul_comm]
    _ ≤ (n : ℝ) / ‖θ‖ ^ 2 * (1 + 100 * Real.sqrt (Real.log n / n)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
