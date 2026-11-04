-- Prove2me | solution 1 for FullyCoupledSDE.DiffApprox.lemma_4_1_mollifier
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:18:27.644599+00:00
-- url     : https://prove2.me/submissions/b9481b09-fee6-4e02-af0d-4c433f44a2a0

import Mathlib
import Definitions.Def_FullyCoupledSDE_DiffApprox_Setting

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace Moll41

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

lemma exp_bound {K : E → ℝ} (hK : Differentiable ℝ K) (h0 : ∀ z, 0 ≤ K z) {a : ℝ}
    (hd : ∀ z, ‖fderiv ℝ K z‖ ≤ a * K z) (z v : E) :
    K (z + v) ≤ Real.exp (a * ‖v‖) * K z := by
  set h : ℝ → ℝ := fun τ => K (z + τ • v) with hh
  have hder : ∀ τ : ℝ, HasDerivAt h (fderiv ℝ K (z + τ • v) v) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => z + τ • v) v τ := by
      simpa using ((hasDerivAt_id τ).smul_const v).const_add z
    exact (hK (z + τ • v)).hasFDerivAt.comp_hasDerivAt τ h1
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le (f := h)
    (f' := fun τ => fderiv ℝ K (z + τ • v) v)
    (δ := K z) (K := a * ‖v‖) (ε := 0) (a := 0) (b := 1)
    (fun τ _ => (hder τ).continuousAt.continuousWithinAt)
    (fun τ _ => (hder τ).hasDerivWithinAt)
    (by simp [h, Real.norm_eq_abs, abs_of_nonneg (h0 z)])
    (fun τ _ => by
      have h3 := (fderiv ℝ K (z + τ • v)).le_opNorm v
      have h2 := hd (z + τ • v)
      simp only [h, Real.norm_eq_abs, abs_of_nonneg (h0 _), add_zero]
      rw [Real.norm_eq_abs] at h3
      calc |fderiv ℝ K (z + τ • v) v| ≤ ‖fderiv ℝ K (z + τ • v)‖ * ‖v‖ := h3
        _ ≤ a * K (z + τ • v) * ‖v‖ := by gcongr
        _ = a * ‖v‖ * K (z + τ • v) := by ring)
    1 (by simp)
  rw [gronwallBound_ε0] at hb
  simpa [h, Real.norm_eq_abs, abs_of_nonneg (h0 _), mul_comm] using hb

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A good first-order kernel. -/
structure Ker (K : E → ℝ) (a1 : ℝ) : Prop where
  cd : ContDiff ℝ 1 K
  nonneg : ∀ z, 0 ≤ K z
  int : Integrable K μ
  a1_nonneg : 0 ≤ a1
  d1 : ∀ z, ‖fderiv ℝ K z‖ ≤ a1 * K z

/-- A good second-order kernel. -/
structure Ker2 (K : E → ℝ) (a1 a2 : ℝ) : Prop extends Ker μ K a1 where
  cd2 : ContDiff ℝ 2 K
  a2_nonneg : 0 ≤ a2
  d2 : ∀ z, ‖fderiv ℝ (fderiv ℝ K) z‖ ≤ a2 * K z

variable {μ}

lemma Ker.diff {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) : Differentiable ℝ K :=
  hK.cd.differentiable (by norm_num)

lemma Ker.cont_fderiv {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) : Continuous (fderiv ℝ K) :=
  hK.cd.continuous_fderiv (by norm_num)

lemma Ker2.diff_fderiv {K : E → ℝ} {a1 a2 : ℝ} (hK : Ker2 μ K a1 a2) :
    Differentiable ℝ (fderiv ℝ K) :=
  (hK.cd2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)

lemma Ker2.cont_fderiv2 {K : E → ℝ} {a1 a2 : ℝ} (hK : Ker2 μ K a1 a2) :
    Continuous (fderiv ℝ (fderiv ℝ K)) :=
  (hK.cd2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)

lemma Ker.shift {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) {y y0 w : E} (hy : y ∈ Metric.ball y0 1) :
    K (y - w) ≤ Real.exp a1 * K (y0 - w) := by
  have h := exp_bound hK.diff hK.nonneg hK.d1 (y0 - w) (y - y0)
  have e : y0 - w + (y - y0) = y - w := by abel
  rw [e] at h
  refine h.trans ?_
  gcongr
  · exact hK.nonneg _
  · rw [Metric.mem_ball, dist_eq_norm] at hy
    nlinarith [hK.a1_nonneg, norm_nonneg (y - y0)]

lemma integrable_of_le_ker {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) {V : Type*}
    [NormedAddCommGroup V] {Q : E → V} (hQ : AEStronglyMeasurable Q μ) {a : ℝ}
    (hb : ∀ z, ‖Q z‖ ≤ a * K z) : Integrable Q μ :=
  (hK.int.const_mul a).mono' hQ (Eventually.of_forall hb)

lemma integrable_sub_of_le_ker {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) {V : Type*}
    [NormedAddCommGroup V] {Q : E → V} (hQ : AEStronglyMeasurable Q μ) {a : ℝ} (y : E)
    (hb : ∀ w, ‖Q w‖ ≤ a * K (y - w)) : Integrable Q μ :=
  ((hK.int.comp_sub_left y).const_mul a).mono' hQ (Eventually.of_forall hb)

/-- Smoothing: first derivative under the integral. -/
lemma hasFDerivAt_S {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) {g : E → ℝ}
    (hg : AEStronglyMeasurable g μ) {M : ℝ} (hM : ∀ w, |g w| ≤ M) (y0 : E) :
    HasFDerivAt (fun y => ∫ w, g w * K (y - w) ∂μ) (∫ w, g w • fderiv ℝ K (y0 - w) ∂μ) y0 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hKc : Continuous K := hK.diff.continuous
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Metric.ball y0 1)
    (F := fun y w => g w * K (y - w)) (F' := fun y w => g w • fderiv ℝ K (y - w))
    (bound := fun w => M * (a1 * (Real.exp a1 * K (y0 - w))))
    (Metric.ball_mem_nhds y0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun y =>
      hg.mul (hKc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine ((hK.int.comp_sub_left y0).const_mul M).mono'
      (hg.mul (hKc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun w => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hK.nonneg _)]
    exact mul_le_mul_of_nonneg_right (hM w) (hK.nonneg _)
  · exact hg.smul (hK.cont_fderiv.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun w y hy => ?_
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul (hM w) ?_ (norm_nonneg _) hM0
    exact (hK.d1 _).trans (mul_le_mul_of_nonneg_left (hK.shift hy) hK.a1_nonneg)
  · exact (((hK.int.comp_sub_left y0).const_mul (Real.exp a1)).const_mul a1).const_mul M
  · refine Eventually.of_forall fun w y _ => ?_
    have h1 := ((hK.diff (y - w)).hasFDerivAt.comp y (hasFDerivAt_sub_const w)).const_mul (g w)
    simpa using h1

/-- Smoothing: second derivative under the integral. -/
lemma hasFDerivAt_S1 {K : E → ℝ} {a1 a2 : ℝ} (hK : Ker2 μ K a1 a2) {g : E → ℝ}
    (hg : AEStronglyMeasurable g μ) {M : ℝ} (hM : ∀ w, |g w| ≤ M) (y0 : E) :
    HasFDerivAt (fun y => ∫ w, g w • fderiv ℝ K (y - w) ∂μ)
      (∫ w, g w • fderiv ℝ (fderiv ℝ K) (y0 - w) ∂μ) y0 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Metric.ball y0 1)
    (F := fun y w => g w • fderiv ℝ K (y - w))
    (F' := fun y w => g w • fderiv ℝ (fderiv ℝ K) (y - w))
    (bound := fun w => M * (a2 * (Real.exp a1 * K (y0 - w))))
    (Metric.ball_mem_nhds y0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun y =>
      hg.smul (hK.cont_fderiv.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine ((hK.int.comp_sub_left y0).const_mul (M * a1)).mono'
      (hg.smul (hK.cont_fderiv.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun w => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul (hM w) (hK.d1 _) (norm_nonneg _) hM0
  · exact hg.smul (hK.cont_fderiv2.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun w y hy => ?_
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul (hM w) ?_ (norm_nonneg _) hM0
    exact (hK.d2 _).trans (mul_le_mul_of_nonneg_left (hK.shift hy) hK.a2_nonneg)
  · exact (((hK.int.comp_sub_left y0).const_mul (Real.exp a1)).const_mul a2).const_mul M
  · refine Eventually.of_forall fun w y _ => ?_
    have h1 := ((hK.diff_fderiv (y - w)).hasFDerivAt.comp y (hasFDerivAt_sub_const w)).const_smul (g w)
    simp only [ContinuousLinearMap.comp_id] at h1
    exact h1


lemma Ker2.bound2 {K : E → ℝ} {a1 a2 : ℝ} (hK : Ker2 μ K a1 a2) {g : E → ℝ}
    {M : ℝ} (hM : ∀ w, |g w| ≤ M) {y y0 : E} (hy : y ∈ Metric.ball y0 1) (w : E) :
    ‖g w • fderiv ℝ (fderiv ℝ K) (y - w)‖ ≤ M * (a2 * (Real.exp a1 * K (y0 - w))) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs]
  refine mul_le_mul (hM w) ?_ (norm_nonneg _) hM0
  exact (hK.d2 _).trans (mul_le_mul_of_nonneg_left (hK.shift hy) hK.a2_nonneg)

lemma continuous_S2 {K : E → ℝ} {a1 a2 : ℝ} (hK : Ker2 μ K a1 a2) {g : E → ℝ}
    (hg : AEStronglyMeasurable g μ) {M : ℝ} (hM : ∀ w, |g w| ≤ M) :
    Continuous (fun y => ∫ w, g w • fderiv ℝ (fderiv ℝ K) (y - w) ∂μ) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine continuous_iff_continuousAt.2 fun y0 => ?_
  refine continuousAt_of_dominated (F := fun y w => g w • fderiv ℝ (fderiv ℝ K) (y - w))
    (bound := fun w => M * (a2 * (Real.exp a1 * K (y0 - w))))
    ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun y =>
      hg.smul (hK.cont_fderiv2.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds y0 one_pos) fun y hy => ?_
    refine Eventually.of_forall fun w => ?_
    exact hK.bound2 hM hy w
  · exact (((hK.int.comp_sub_left y0).const_mul (Real.exp a1)).const_mul a2).const_mul M
  · exact Eventually.of_forall fun w =>
      ((continuous_const (y := g w)).smul
        (hK.cont_fderiv2.comp (continuous_id.sub (continuous_const (y := w))))).continuousAt

lemma integral_fderiv_zero {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) (y : E) :
    ∫ w, fderiv ℝ K (y - w) ∂μ = 0 := by
  have h := hasFDerivAt_S hK (g := fun _ => (1:ℝ)) aestronglyMeasurable_const
    (M := 1) (fun _ => by simp) y
  have hc : (fun y => ∫ w, (fun _ => (1:ℝ)) w * K (y - w) ∂μ) = fun _ => ∫ z, K z ∂μ := by
    funext y'
    simp only [one_mul]
    exact integral_sub_left_eq_self K μ y'
  rw [hc] at h
  have := h.unique (hasFDerivAt_const _ _)
  simpa using this

lemma integral_fderiv2_zero {K : E → ℝ} {a1 a2 : ℝ} (hK : Ker2 μ K a1 a2) (y : E) :
    ∫ w, fderiv ℝ (fderiv ℝ K) (y - w) ∂μ = 0 := by
  have h := hasFDerivAt_S1 hK (g := fun _ => (1:ℝ)) aestronglyMeasurable_const
    (M := 1) (fun _ => by simp) y
  have hc : (fun y => ∫ w, (fun _ => (1:ℝ)) w • fderiv ℝ K (y - w) ∂μ) =
      fun _ => ∫ z, fderiv ℝ K z ∂μ := by
    funext y'
    simp only [one_smul]
    exact integral_sub_left_eq_self (fderiv ℝ K) μ y'
  rw [hc] at h
  have := h.unique (hasFDerivAt_const _ _)
  simpa using this

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma fderiv_comp_neg' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : E → V}
    (hφ : Differentiable ℝ φ) (z : E) :
    fderiv ℝ (fun z => φ (-z)) z = -fderiv ℝ φ (-z) := by
  have h : HasFDerivAt (fun z => φ (-z)) _ z := (hφ (-z)).hasFDerivAt.comp z ((hasFDerivAt_id z).neg)
  rw [h.fderiv]
  ext v
  simp

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma fderiv_even {K : E → ℝ} (hK : Differentiable ℝ K) (he : ∀ z, K (-z) = K z) (z : E) :
    fderiv ℝ K (-z) = -fderiv ℝ K z := by
  have h := fderiv_comp_neg' hK z
  have e : (fun z => K (-z)) = K := funext he
  rw [e] at h
  rw [h, neg_neg]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma fderiv2_even {K : E → ℝ} (hK : Differentiable ℝ K) (hK2 : Differentiable ℝ (fderiv ℝ K))
    (he : ∀ z, K (-z) = K z) (z : E) :
    fderiv ℝ (fderiv ℝ K) (-z) = fderiv ℝ (fderiv ℝ K) z := by
  have h := fderiv_comp_neg' hK2 z
  have e : (fun z => fderiv ℝ K (-z)) = fun z => -fderiv ℝ K z := funext (fderiv_even hK he)
  rw [e, fderiv_fun_neg] at h
  exact neg_injective h.symm

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma integral_odd_zero [μ.IsNegInvariant] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : E → V} (hΦ : ∀ z, Φ (-z) = -Φ z) : ∫ z, Φ z ∂μ = 0 := by
  have h : ∫ z, Φ z ∂μ = -∫ z, Φ z ∂μ := by
    calc ∫ z, Φ z ∂μ = ∫ z, Φ (-z) ∂μ := (integral_neg_eq_self Φ μ).symm
      _ = ∫ z, -Φ z ∂μ := by congr 1; funext z; exact hΦ z
      _ = -∫ z, Φ z ∂μ := integral_neg (fun z => Φ z)
  have h2 : (2:ℝ) • ∫ z, Φ z ∂μ = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  simpa using h2


/-- Generic cancellation bound for a kernel derivative `D`. -/
lemma norm_SD_le {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : E → V} (hDc : Continuous D) {a : ℝ} (hDb : ∀ z, ‖D z‖ ≤ a * K z)
    (hD0 : ∀ y, ∫ w, D (y - w) ∂μ = 0)
    {g : E → ℝ} (hg : AEStronglyMeasurable g μ) {M : ℝ} (hM : ∀ w, |g w| ≤ M) {y : E}
    {L p : ℝ} (ℓ : E →L[ℝ] ℝ)
    (hℓ : ℓ = 0 ∨ (Integrable (fun z => ‖z‖ * K z) μ ∧ ∀ z, D (-z) = D z))
    (hL : ∀ w, |g w - g y - ℓ (w - y)| ≤ L * ‖w - y‖ ^ p)
    (hmom : Integrable (fun z => ‖z‖ ^ p * K z) μ) :
    ‖∫ w, g w • D (y - w) ∂μ‖ ≤ L * a * ∫ z, ‖z‖ ^ p * K z ∂μ := by
  have hDm : AEStronglyMeasurable (fun w => D (y - w)) μ :=
    (hDc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint1 : Integrable (fun w => g w • D (y - w)) μ := by
    refine ((hK.int.comp_sub_left y).const_mul (M * a)).mono' (hg.smul hDm)
      (Eventually.of_forall fun w => ?_)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul (hM w) (hDb _) (norm_nonneg _) hM0
  have hint2 : Integrable (fun w => g y • D (y - w)) μ := by
    refine ((hK.int.comp_sub_left y).const_mul (|g y| * a)).mono'
      (hDm.const_smul (g y)) (Eventually.of_forall fun w => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hDb _) (abs_nonneg _)
  have hint3 : Integrable (fun w => ℓ (w - y) • D (y - w)) μ := by
    rcases hℓ with h0 | ⟨h1, _⟩
    · simp [h0]
    · refine ((h1.comp_sub_left y).const_mul (‖ℓ‖ * a)).mono'
        (((ℓ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).smul hDm)
        (Eventually.of_forall fun w => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      have h2 := ℓ.le_opNorm (w - y)
      rw [Real.norm_eq_abs] at h2
      have ha : 0 ≤ a * K (y - w) := (norm_nonneg _).trans (hDb _)
      calc |ℓ (w - y)| * ‖D (y - w)‖ ≤ (‖ℓ‖ * ‖w - y‖) * (a * K (y - w)) :=
            mul_le_mul h2 (hDb _) (norm_nonneg _) (by positivity)
        _ = ‖ℓ‖ * a * (‖y - w‖ * K (y - w)) := by rw [norm_sub_rev]; ring
  have hodd : ∫ w, ℓ (w - y) • D (y - w) ∂μ = 0 := by
    rcases hℓ with h0 | ⟨_, hev⟩
    · simp [h0]
    have e1 : ∫ w, ℓ (w - y) • D (y - w) ∂μ = ∫ z, ℓ (-z) • D z ∂μ := by
      rw [← integral_sub_left_eq_self (fun z => ℓ (-z) • D z) μ y]
      simp only [neg_sub]
    rw [e1]
    refine integral_odd_zero fun z => ?_
    simp only [neg_neg, map_neg, neg_smul, hev]
  have heq : ∫ w, g w • D (y - w) ∂μ = ∫ w, (g w - g y - ℓ (w - y)) • D (y - w) ∂μ := by
    simp_rw [sub_smul]
    rw [integral_sub (f := fun w => g w • D (y - w) - g y • D (y - w))
      (g := fun w => ℓ (w - y) • D (y - w)) (hint1.sub hint2) hint3,
      integral_sub hint1 hint2, integral_smul,
      hD0, hodd, smul_zero, sub_zero, sub_zero]
  rw [heq]
  have hmom' := (hmom.comp_sub_left y).const_mul (L * a)
  refine (norm_integral_le_of_norm_le hmom' (Eventually.of_forall fun w => ?_)).trans_eq ?_
  · rw [norm_smul, Real.norm_eq_abs]
    have h1 := hL w
    have h2 := hDb (y - w)
    have h3 : 0 ≤ L * ‖w - y‖ ^ p := (abs_nonneg _).trans h1
    calc |g w - g y - ℓ (w - y)| * ‖D (y - w)‖ ≤ (L * ‖w - y‖ ^ p) * (a * K (y - w)) :=
          mul_le_mul h1 h2 (norm_nonneg _) h3
      _ = L * a * (‖y - w‖ ^ p * K (y - w)) := by rw [norm_sub_rev]; ring
  · rw [integral_const_mul]
    congr 1
    exact integral_sub_left_eq_self (fun z => ‖z‖ ^ p * K z) μ y

/-- First-order cancellation bound. -/
lemma norm_S1_le {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) {g : E → ℝ}
    (hg : AEStronglyMeasurable g μ) {M : ℝ} (hM : ∀ w, |g w| ≤ M) {y : E} {L p : ℝ}
    (hL : ∀ w, |g w - g y| ≤ L * ‖w - y‖ ^ p)
    (hmom : Integrable (fun z => ‖z‖ ^ p * K z) μ) :
    ‖∫ w, g w • fderiv ℝ K (y - w) ∂μ‖ ≤ L * a1 * ∫ z, ‖z‖ ^ p * K z ∂μ :=
  norm_SD_le hK hK.cont_fderiv hK.d1 (integral_fderiv_zero hK) hg hM 0 (Or.inl rfl)
    (by simpa using hL) hmom

/-- Second-order cancellation bound. -/
lemma norm_S2_le {K : E → ℝ} {a1 a2 : ℝ} (hK : Ker2 μ K a1 a2) (he : ∀ z, K (-z) = K z)
    {g : E → ℝ} (hg : AEStronglyMeasurable g μ) {M : ℝ} (hM : ∀ w, |g w| ≤ M) {y : E}
    {L p : ℝ} (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ = 0 ∨ Integrable (fun z => ‖z‖ * K z) μ)
    (hL : ∀ w, |g w - g y - ℓ (w - y)| ≤ L * ‖w - y‖ ^ p)
    (hmom : Integrable (fun z => ‖z‖ ^ p * K z) μ) :
    ‖∫ w, g w • fderiv ℝ (fderiv ℝ K) (y - w) ∂μ‖ ≤ L * a2 * ∫ z, ‖z‖ ^ p * K z ∂μ :=
  norm_SD_le hK.toKer hK.cont_fderiv2 hK.d2 (integral_fderiv2_zero hK) hg hM ℓ
    (hℓ.imp_right fun h => ⟨h, fderiv2_even hK.diff hK.diff_fderiv he⟩) hL hmom

/-- Zeroth-order cancellation bound. -/
lemma abs_S_sub_le {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) (he : ∀ z, K (-z) = K z)
    (hK1 : ∫ z, K z ∂μ = 1)
    {g : E → ℝ} (hg : AEStronglyMeasurable g μ) {M : ℝ} (hM : ∀ w, |g w| ≤ M) {y : E}
    {L p : ℝ} (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ = 0 ∨ Integrable (fun z => ‖z‖ * K z) μ)
    (hL : ∀ w, |g w - g y - ℓ (w - y)| ≤ L * ‖w - y‖ ^ p)
    (hmom : Integrable (fun z => ‖z‖ ^ p * K z) μ) :
    |∫ w, g w * K (y - w) ∂μ - g y| ≤ L * ∫ z, ‖z‖ ^ p * K z ∂μ := by
  have hKm : AEStronglyMeasurable (fun w => K (y - w)) μ :=
    (hK.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint1 : Integrable (fun w => g w * K (y - w)) μ := by
    refine ((hK.int.comp_sub_left y).const_mul M).mono' (hg.mul hKm)
      (Eventually.of_forall fun w => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hK.nonneg _)]
    exact mul_le_mul_of_nonneg_right (hM w) (hK.nonneg _)
  have hint2 : Integrable (fun w => g y * K (y - w)) μ := (hK.int.comp_sub_left y).const_mul _
  have hint3 : Integrable (fun w => ℓ (w - y) * K (y - w)) μ := by
    rcases hℓ with h0 | h1
    · simp [h0]
    · refine ((h1.comp_sub_left y).const_mul (‖ℓ‖)).mono'
        (((ℓ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).mul hKm)
        (Eventually.of_forall fun w => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hK.nonneg _)]
      have h2 := ℓ.le_opNorm (w - y)
      rw [Real.norm_eq_abs] at h2
      calc |ℓ (w - y)| * K (y - w) ≤ (‖ℓ‖ * ‖w - y‖) * K (y - w) :=
            mul_le_mul_of_nonneg_right h2 (hK.nonneg _)
        _ = ‖ℓ‖ * (‖y - w‖ * K (y - w)) := by rw [norm_sub_rev]; ring
  have hodd : ∫ w, ℓ (w - y) * K (y - w) ∂μ = 0 := by
    have e1 : ∫ w, ℓ (w - y) * K (y - w) ∂μ = ∫ z, ℓ (-z) * K z ∂μ := by
      rw [← integral_sub_left_eq_self (fun z => ℓ (-z) * K z) μ y]
      simp only [neg_sub]
    rw [e1]
    refine integral_odd_zero fun z => ?_
    simp only [neg_neg, map_neg, neg_mul, he]
  have hc : ∫ w, g y * K (y - w) ∂μ = g y := by
    rw [integral_const_mul, integral_sub_left_eq_self K μ y, hK1, mul_one]
  have heq : ∫ w, g w * K (y - w) ∂μ - g y = ∫ w, (g w - g y - ℓ (w - y)) * K (y - w) ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub (f := fun w => g w * K (y - w) - g y * K (y - w))
      (g := fun w => ℓ (w - y) * K (y - w)) (hint1.sub hint2) hint3,
      integral_sub hint1 hint2, hc, hodd, sub_zero]
  rw [heq, ← Real.norm_eq_abs]
  have hmom' := (hmom.comp_sub_left y).const_mul L
  refine (norm_integral_le_of_norm_le hmom' (Eventually.of_forall fun w => ?_)).trans_eq ?_
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hK.nonneg _)]
    have h1 := hL w
    calc |g w - g y - ℓ (w - y)| * K (y - w) ≤ (L * ‖w - y‖ ^ p) * K (y - w) :=
          mul_le_mul_of_nonneg_right h1 (hK.nonneg _)
      _ = L * (‖y - w‖ ^ p * K (y - w)) := by rw [norm_sub_rev]; ring
  · rw [integral_const_mul]
    congr 1
    exact integral_sub_left_eq_self (fun z => ‖z‖ ^ p * K z) μ y


section Scale

variable (μ) in
/-- Scaled kernel facts. -/
structure Base (ρ : E → ℝ) (A1 A2 : ℝ) : Prop where
  cd : ContDiff ℝ 2 ρ
  nonneg : ∀ z, 0 ≤ ρ z
  int : Integrable ρ μ
  A1_nonneg : 0 ≤ A1
  A2_nonneg : 0 ≤ A2
  d1 : ∀ z, ‖fderiv ℝ ρ z‖ ≤ A1 * ρ z
  d2 : ∀ z, ‖fderiv ℝ (fderiv ℝ ρ) z‖ ≤ A2 * ρ z

/-- The rescaled kernel `c^d ρ(c z)`. -/
noncomputable def sc (ρ : E → ℝ) (c : ℝ) (z : E) : ℝ := c ^ Module.finrank ℝ E * ρ (c • z)

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma hasFDerivAt_sc {ρ : E → ℝ} (hρ : Differentiable ℝ ρ) (c : ℝ) (z : E) :
    HasFDerivAt (sc ρ c) ((c ^ Module.finrank ℝ E * c) • fderiv ℝ ρ (c • z)) z := by
  have h1 : HasFDerivAt (fun z : E => c • z) (c • ContinuousLinearMap.id ℝ E) z :=
    (hasFDerivAt_id z).const_smul c
  have h2 := ((hρ (c • z)).hasFDerivAt.comp z h1).const_mul (c ^ Module.finrank ℝ E)
  have e : (c ^ Module.finrank ℝ E * c) • fderiv ℝ ρ (c • z) =
      c ^ Module.finrank ℝ E • (fderiv ℝ ρ (c • z)).comp (c • ContinuousLinearMap.id ℝ E) := by
    ext v
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    ring
  rw [e]
  exact h2

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma fderiv_sc {ρ : E → ℝ} (hρ : Differentiable ℝ ρ) (c : ℝ) :
    fderiv ℝ (sc ρ c) = fun z => (c ^ Module.finrank ℝ E * c) • fderiv ℝ ρ (c • z) :=
  funext fun z => (hasFDerivAt_sc hρ c z).fderiv

lemma Base.ker2 {ρ : E → ℝ} {A1 A2 : ℝ} (hρ : Base μ ρ A1 A2) {c : ℝ} (hc : 0 < c) :
    Ker2 μ (sc ρ c) (A1 * c) (A2 * c ^ 2) := by
  have hdiff : Differentiable ℝ ρ := hρ.cd.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (fderiv ℝ ρ) :=
    (hρ.cd.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hcd : ContDiff ℝ 2 (sc ρ c) :=
    contDiff_const.mul (hρ.cd.comp (contDiff_id.const_smul c))
  have hcd0 : 0 ≤ c ^ Module.finrank ℝ E := by positivity
  refine
    { cd := hcd.of_le (by norm_num)
      nonneg := fun z => mul_nonneg hcd0 (hρ.nonneg _)
      int := ?_
      a1_nonneg := mul_nonneg hρ.A1_nonneg hc.le
      d1 := ?_
      cd2 := hcd
      a2_nonneg := mul_nonneg hρ.A2_nonneg (by positivity)
      d2 := ?_ }
  · exact (hρ.int.comp_smul hc.ne').const_mul _
  · intro z
    rw [fderiv_sc hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc c ^ Module.finrank ℝ E * c * ‖fderiv ℝ ρ (c • z)‖
        ≤ c ^ Module.finrank ℝ E * c * (A1 * ρ (c • z)) := by gcongr; exact hρ.d1 _
      _ = A1 * c * sc ρ c z := by simp only [sc]; ring
  · intro z
    rw [fderiv_sc hdiff]
    have h1 : HasFDerivAt (fun z : E => c • z) (c • ContinuousLinearMap.id ℝ E) z :=
      (hasFDerivAt_id z).const_smul c
    have h2 : HasFDerivAt (fun z => (c ^ Module.finrank ℝ E * c) • fderiv ℝ ρ (c • z)) _ z :=
      ((hdiff2 (c • z)).hasFDerivAt.comp z h1).const_smul (c ^ Module.finrank ℝ E * c)
    rw [h2.fderiv]
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h3 : ‖(fderiv ℝ (fderiv ℝ ρ) (c • z)).comp (c • ContinuousLinearMap.id ℝ E)‖ ≤
        ‖fderiv ℝ (fderiv ℝ ρ) (c • z)‖ * c := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      gcongr
      refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
      rw [Real.norm_eq_abs, abs_of_pos hc]
      calc c * ‖ContinuousLinearMap.id ℝ E‖ ≤ c * 1 := by
            gcongr; exact ContinuousLinearMap.norm_id_le
        _ = c := mul_one c
    calc c ^ Module.finrank ℝ E * c *
          ‖(fderiv ℝ (fderiv ℝ ρ) (c • z)).comp (c • ContinuousLinearMap.id ℝ E)‖
        ≤ c ^ Module.finrank ℝ E * c * (‖fderiv ℝ (fderiv ℝ ρ) (c • z)‖ * c) := by gcongr
      _ ≤ c ^ Module.finrank ℝ E * c * ((A2 * ρ (c • z)) * c) := by
          gcongr; exact hρ.d2 _
      _ = A2 * c ^ 2 * sc ρ c z := by simp only [sc]; ring

lemma integral_sc (ρ : E → ℝ) {c : ℝ} (hc : 0 < c) : ∫ z, sc ρ c z ∂μ = ∫ z, ρ z ∂μ := by
  simp only [sc]
  rw [integral_const_mul, Measure.integral_comp_smul, smul_eq_mul, abs_of_pos (by positivity),
    ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

lemma moment_sc (ρ : E → ℝ) {c : ℝ} (hc : 0 < c) (p : ℝ) :
    ∫ z, ‖z‖ ^ p * sc ρ c z ∂μ = c ^ (-p) * ∫ u, ‖u‖ ^ p * ρ u ∂μ := by
  have e : (fun z : E => ‖z‖ ^ p * sc ρ c z) =
      fun z => (c ^ (-p) * c ^ Module.finrank ℝ E) * (‖c • z‖ ^ p * ρ (c • z)) := by
    funext z
    simp only [sc]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, Real.mul_rpow hc.le (norm_nonneg _)]
    have : c ^ (-p) * c ^ p = 1 := by
      rw [← Real.rpow_add hc]; simp
    calc ‖z‖ ^ p * (c ^ Module.finrank ℝ E * ρ (c • z))
        = (c ^ (-p) * c ^ p) * ‖z‖ ^ p * (c ^ Module.finrank ℝ E * ρ (c • z)) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [e, integral_const_mul,
    Measure.integral_comp_smul μ (fun u => ‖u‖ ^ p * ρ u) c, smul_eq_mul,
    abs_of_pos (by positivity)]
  field_simp

lemma moment_sc_int {ρ : E → ℝ} {c : ℝ} (hc : 0 < c) {p : ℝ}
    (h : Integrable (fun u => ‖u‖ ^ p * ρ u) μ) :
    Integrable (fun z => ‖z‖ ^ p * sc ρ c z) μ := by
  have e : (fun z : E => ‖z‖ ^ p * sc ρ c z) =
      fun z => (c ^ (-p) * c ^ Module.finrank ℝ E) * (‖c • z‖ ^ p * ρ (c • z)) := by
    funext z
    simp only [sc]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, Real.mul_rpow hc.le (norm_nonneg _)]
    have : c ^ (-p) * c ^ p = 1 := by
      rw [← Real.rpow_add hc]; simp
    calc ‖z‖ ^ p * (c ^ Module.finrank ℝ E * ρ (c • z))
        = (c ^ (-p) * c ^ p) * ‖z‖ ^ p * (c ^ Module.finrank ℝ E * ρ (c • z)) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [e]
  exact (h.comp_smul hc.ne').const_mul _

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma sc_even {ρ : E → ℝ} (he : ∀ z, ρ (-z) = ρ z) (c : ℝ) (z : E) : sc ρ c (-z) = sc ρ c z := by
  simp only [sc, smul_neg, he]

end Scale

end Moll41

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace Moll41

section Reg

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

lemma iFD0_eq (g : E → F) (y : E) :
    iteratedFDeriv ℝ 0 g y = (continuousMultilinearCurryFin0 ℝ E F).symm (g y) := by
  rw [iteratedFDeriv_zero_eq_comp]; rfl

lemma iFD1_eq (g : E → F) (y : E) :
    iteratedFDeriv ℝ 1 g y = (continuousMultilinearCurryFin1 ℝ E F).symm (fderiv ℝ g y) := by
  ext m; simp [iteratedFDeriv_one_apply]

lemma norm_iFD0_sub (g : E → F) (y y' : E) :
    ‖iteratedFDeriv ℝ 0 g y - iteratedFDeriv ℝ 0 g y'‖ = ‖g y - g y'‖ := by
  rw [iFD0_eq, iFD0_eq, ← map_sub, LinearIsometryEquiv.norm_map]

lemma norm_iFD1_sub (g : E → F) (y y' : E) :
    ‖iteratedFDeriv ℝ 1 g y - iteratedFDeriv ℝ 1 g y'‖ = ‖fderiv ℝ g y - fderiv ℝ g y'‖ := by
  rw [iFD1_eq, iFD1_eq, ← map_sub, LinearIsometryEquiv.norm_map]

lemma diff_of_iFD0 {g : E → F} (h : Differentiable ℝ (iteratedFDeriv ℝ 0 g)) :
    Differentiable ℝ g := by
  have e : iteratedFDeriv ℝ 0 g = (continuousMultilinearCurryFin0 ℝ E F).symm ∘ g :=
    iteratedFDeriv_zero_eq_comp
  rw [e] at h
  exact (LinearIsometryEquiv.comp_differentiable_iff _).1 h

lemma diff_of_iFD1 {g : E → F} (h : Differentiable ℝ (iteratedFDeriv ℝ 1 g)) :
    Differentiable ℝ (fderiv ℝ g) := by
  have e : iteratedFDeriv ℝ 1 g = (continuousMultilinearCurryFin1 ℝ E F).symm ∘ fderiv ℝ g :=
    funext (iFD1_eq g)
  rw [e] at h
  exact (LinearIsometryEquiv.comp_differentiable_iff _).1 h

lemma norm_iFD2 (g : E → F) (y : E) :
    ‖iteratedFDeriv ℝ 2 g y‖ = ‖fderiv ℝ (fderiv ℝ g) y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

/-- Hölder implies continuity. -/
lemma continuous_of_holder {g : E → ℝ} {L a : ℝ} (ha : 0 < a)
    (h : ∀ y y', |g y' - g y| ≤ L * ‖y' - y‖ ^ a) : Continuous g := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun y' : E => L * ‖y' - y‖ ^ a) (𝓝 y) (𝓝 (L * ‖y - y‖ ^ a)) := by
    refine tendsto_const_nhds.mul ?_
    exact ((continuous_id.sub continuous_const).norm.rpow_const fun _ => Or.inr ha.le).tendsto y
  simp only [sub_self, norm_zero, Real.zero_rpow ha.ne', mul_zero] at h1
  refine squeeze_zero (fun _ => norm_nonneg _) (fun y' => ?_) h1
  rw [Real.norm_eq_abs]
  exact h y y'


/-- The linear Taylor part used when `ϑ ≥ 1`. -/
noncomputable def lin (ϑ : ℝ) (g : E → ℝ) (y : E) : E →L[ℝ] ℝ :=
  if 1 ≤ ϑ then fderiv ℝ g y else 0

/-- Taylor remainder via the mean value theorem on a ball. -/
lemma taylor_ball {g : E → ℝ} (hg : Differentiable ℝ g) {y y' : E} {B : ℝ}
    (hB : ∀ z, ‖z - y‖ ≤ ‖y' - y‖ → ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ B) :
    |g y' - g y - fderiv ℝ g y (y' - y)| ≤ B * ‖y' - y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := g)
    (s := Metric.closedBall y ‖y' - y‖) (x := y) (y := y') (φ := fderiv ℝ g y)
    (fun z _ => hg z) (fun z hz => hB z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz))
    (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm])
  rwa [Real.norm_eq_abs] at h

end Reg

section Param

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma cont_param {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : E → V} (hDc : Continuous D) {a : ℝ} (hDb : ∀ z, ‖D z‖ ≤ a * K z)
    {G : ℝ → E → ℝ} (hGc : ∀ w, Continuous fun u => G u w) (hGm : ∀ u, Continuous (G u))
    {M : ℝ} (hGb : ∀ u w, |G u w| ≤ M) (y : E) :
    Continuous (fun u => ∫ w, G u w • D (y - w) ∂μ) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hGb 0 0)
  refine continuous_of_dominated (F := fun u w => G u w • D (y - w))
    (bound := fun w => M * (a * K (y - w)))
    (fun u => (hGm u).aestronglyMeasurable.smul
      (hDc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (fun u => Eventually.of_forall fun w => ?_) (((hK.int.comp_sub_left y).const_mul a).const_mul M)
    (Eventually.of_forall fun w => (hGc w).smul continuous_const)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hGb u w) (hDb _) (norm_nonneg _) hM0

lemma crude_bound {K : E → ℝ} {a1 : ℝ} (hK : Ker μ K a1) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {D : E → V} {a : ℝ} (hDb : ∀ z, ‖D z‖ ≤ a * K z)
    {g : E → ℝ} {M : ℝ} (hM : ∀ w, |g w| ≤ M) (y : E) :
    ‖∫ w, g w • D (y - w) ∂μ‖ ≤ M * a * ∫ z, K z ∂μ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine (norm_integral_le_of_norm_le ((hK.int.comp_sub_left y).const_mul (M * a))
    (Eventually.of_forall fun w => ?_)).trans_eq ?_
  · rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul (hM w) (hDb _) (norm_nonneg _) hM0
  · rw [integral_const_mul, integral_sub_left_eq_self K μ y]

end Param

section Outer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiating `y ↦ ∫ Ψ_s(y) k(s) ds` twice under the integral. -/
lemma outer_C2 {k : ℝ → ℝ} (hk : Integrable k) (hk0 : ∀ s, 0 ≤ k s)
    {Ψ : ℝ → E → ℝ} {Ψ1 : ℝ → E → (E →L[ℝ] ℝ)} {Ψ2 : ℝ → E → (E →L[ℝ] E →L[ℝ] ℝ)}
    (h0 : ∀ s y, HasFDerivAt (Ψ s) (Ψ1 s y) y) (h1 : ∀ s y, HasFDerivAt (Ψ1 s) (Ψ2 s y) y)
    (h2 : ∀ s, Continuous (Ψ2 s))
    (m0 : ∀ y, AEStronglyMeasurable (fun s => Ψ s y))
    (m1 : ∀ y, AEStronglyMeasurable (fun s => Ψ1 s y))
    (m2 : ∀ y, AEStronglyMeasurable (fun s => Ψ2 s y))
    {B0 B1 B2 : ℝ} (b0 : ∀ s y, |Ψ s y| ≤ B0) (b1 : ∀ s y, ‖Ψ1 s y‖ ≤ B1)
    (b2 : ∀ s y, ‖Ψ2 s y‖ ≤ B2) :
    ContDiff ℝ 2 (fun y => ∫ s, Ψ s y * k s) ∧
      ∀ y, ‖fderiv ℝ (fderiv ℝ (fun y => ∫ s, Ψ s y * k s)) y‖ ≤ B2 * ∫ s, k s := by
  set Φ1 : E → (E →L[ℝ] ℝ) := fun y => ∫ s, k s • Ψ1 s y with hΦ1
  set Φ2 : E → (E →L[ℝ] E →L[ℝ] ℝ) := fun y => ∫ s, k s • Ψ2 s y with hΦ2
  have hd0 : ∀ y0, HasFDerivAt (fun y => ∫ s, Ψ s y * k s) (Φ1 y0) y0 := by
    intro y0
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (F := fun y s => Ψ s y * k s) (F' := fun y s => k s • Ψ1 s y)
      (bound := fun s => k s * B1) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun y => (m0 y).mul hk.aestronglyMeasurable
    · refine (hk.mul_const B0).mono' ((m0 y0).mul hk.aestronglyMeasurable)
        (Eventually.of_forall fun s => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hk0 s), mul_comm]
      exact mul_le_mul_of_nonneg_left (b0 s y0) (hk0 s)
    · exact hk.aestronglyMeasurable.smul (m1 y0)
    · refine Eventually.of_forall fun s y _ => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hk0 s)]
      exact mul_le_mul_of_nonneg_left (b1 s y) (hk0 s)
    · exact hk.mul_const B1
    · exact Eventually.of_forall fun s y _ => (h0 s y).mul_const (k s)
  have hd1 : ∀ y0, HasFDerivAt Φ1 (Φ2 y0) y0 := by
    intro y0
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (F := fun y s => k s • Ψ1 s y) (F' := fun y s => k s • Ψ2 s y)
      (bound := fun s => k s * B2) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun y => hk.aestronglyMeasurable.smul (m1 y)
    · refine (hk.mul_const B1).mono' (hk.aestronglyMeasurable.smul (m1 y0))
        (Eventually.of_forall fun s => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hk0 s)]
      exact mul_le_mul_of_nonneg_left (b1 s y0) (hk0 s)
    · exact hk.aestronglyMeasurable.smul (m2 y0)
    · refine Eventually.of_forall fun s y _ => ?_
      refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hk0 s)]
      exact mul_le_mul_of_nonneg_left (b2 s y) (hk0 s)
    · exact hk.mul_const B2
    · exact Eventually.of_forall fun s y _ => (h1 s y).const_smul (k s)
  have hc2 : Continuous Φ2 := by
    refine continuous_of_dominated (F := fun y s => k s • Ψ2 s y) (bound := fun s => k s * B2)
      (fun y => hk.aestronglyMeasurable.smul (m2 y)) (fun y => Eventually.of_forall fun s => ?_)
      (hk.mul_const B2) (Eventually.of_forall fun s => (continuous_const (y := k s)).smul (h2 s))
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hk0 s)]
    exact mul_le_mul_of_nonneg_left (b2 s y) (hk0 s)
  have hcd1 : ContDiff ℝ 1 Φ1 := by
    have : ContDiff ℝ ((0 : ℕ) + 1) Φ1 :=
      contDiff_succ_iff_hasFDerivAt.2 ⟨Φ2, contDiff_zero.2 hc2, hd1⟩
    simpa using this
  have hcd : ContDiff ℝ 2 (fun y => ∫ s, Ψ s y * k s) := by
    have : ContDiff ℝ ((1 : ℕ) + 1) (fun y => ∫ s, Ψ s y * k s) :=
      contDiff_succ_iff_hasFDerivAt.2 ⟨Φ1, by simpa using hcd1, hd0⟩
    exact this
  refine ⟨hcd, fun y => ?_⟩
  have e1 : fderiv ℝ (fun y => ∫ s, Ψ s y * k s) = Φ1 := funext fun y => (hd0 y).fderiv
  rw [e1, (hd1 y).fderiv]
  refine (norm_integral_le_of_norm_le (hk.mul_const B2) (Eventually.of_forall fun s => ?_)).trans
    ?_
  · refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hk0 s)]
    exact mul_le_mul_of_nonneg_left (b2 s y) (hk0 s)
  · rw [integral_mul_const, mul_comm]

/-- Weighted average bound. -/
lemma avg_bound {k : ℝ → ℝ} (hk0 : ∀ s, 0 ≤ k s) (hki : Integrable k) (hk1 : ∫ s, k s = 1)
    {A : ℝ → ℝ} (hA : AEStronglyMeasurable A) {M : ℝ} (hAM : ∀ s, |A s| ≤ M) {c B D p : ℝ}
    (hmom : Integrable (fun s => |s| ^ p * k s))
    (h : ∀ s, |A s - c| ≤ B + D * |s| ^ p) :
    |(∫ s, A s * k s) - c| ≤ B + D * ∫ s, |s| ^ p * k s := by
  have hint1 : Integrable (fun s => A s * k s) := by
    refine (hki.mul_const M).mono' (hA.mul hki.aestronglyMeasurable)
      (Eventually.of_forall fun s => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hk0 s), mul_comm]
    exact mul_le_mul_of_nonneg_left (hAM s) (hk0 s)
  have hc : ∫ s, c * k s = c := by rw [integral_const_mul, hk1, mul_one]
  have heq : (∫ s, A s * k s) - c = ∫ s, (A s - c) * k s := by
    simp_rw [sub_mul]
    rw [integral_sub hint1 (hki.const_mul c), hc]
  rw [heq, ← Real.norm_eq_abs]
  have hb : Integrable (fun s => B * k s + D * (|s| ^ p * k s)) :=
    (hki.const_mul B).add (hmom.const_mul D)
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun s => ?_)).trans_eq ?_
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hk0 s)]
    calc |A s - c| * k s ≤ (B + D * |s| ^ p) * k s := mul_le_mul_of_nonneg_right (h s) (hk0 s)
      _ = B * k s + D * (|s| ^ p * k s) := by ring
  · rw [integral_add (hki.const_mul B) (hmom.const_mul D), integral_const_mul,
      integral_const_mul, hk1, mul_one]

end Outer

section RegF

open FullyCoupledSDE.DiffApprox

lemma reg_of_CpT {d1 d2 : ℕ} {δ ϑ : ℝ} (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hϑ : ϑ ∈ Set.Ioc (0 : ℝ) 2)
    {f : ℝ → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → ℝ}
    (hf : CpT (ϑ / 2) δ ϑ f) :
    ∃ C > (0 : ℝ), ∃ m > (0 : ℝ), ∀ x : FullyCoupledSDE.Poisson.E d1,
      (∀ u y, |f u x y| ≤ C * (1 + ‖x‖ ^ m)) ∧
      (∀ u u' y, |f u x y - f u' x y| ≤ C * |u - u'| ^ (ϑ / 2) * (1 + ‖x‖ ^ m)) ∧
      (∀ u, Continuous (f u x)) ∧
      (∀ u y, ‖lin ϑ (f u x) y‖ ≤ C * (1 + ‖x‖ ^ m)) ∧
      (∀ u y y', |f u x y' - f u x y - lin ϑ (f u x) y (y' - y)| ≤
        2 * C * (1 + ‖x‖ ^ m) * ‖y' - y‖ ^ ϑ) := by
  obtain ⟨C, hC, m, hm, hcore, htime⟩ := hf
  refine ⟨C, hC, m, hm, fun x => ?_⟩
  have hδ0 : δ ≠ 0 := hδ.1.ne'
  have hW : 0 < 1 + ‖x‖ ^ m := by positivity
  have hW2 : 1 + ‖x‖ ^ m + ‖x‖ ^ m ≤ 2 * (1 + ‖x‖ ^ m) := by
    nlinarith [Real.rpow_nonneg (norm_nonneg x) m]
  have htime' : ∀ u u' y, |f u x y - f u' x y| ≤ C * |u - u'| ^ (ϑ / 2) * (1 + ‖x‖ ^ m) := by
    intro u u' y
    have := htime u u' x y
    rwa [Real.norm_eq_abs, Real.dist_eq] at this
  simp only [HolderCore] at hcore
  have hk1 : (⌊ϑ⌋₊ : ℝ) ≤ ϑ := Nat.floor_le hϑ.1.le
  have hk2 : ϑ < ⌊ϑ⌋₊ + 1 := Nat.lt_floor_add_one ϑ
  have hk3 : ⌊ϑ⌋₊ ≤ 2 := Nat.floor_le_of_le hϑ.2
  generalize hk : ⌊ϑ⌋₊ = k at hcore hk1 hk2 hk3
  interval_cases k
  · -- ϑ < 1
    simp only [Nat.cast_zero, sub_zero] at hcore hk1 hk2
    have H := fun u => (hcore u).2.2.2 hϑ.1.ne'
    have hlin : ∀ u y, lin ϑ (f u x) y = 0 := fun u y => by simp [lin, not_le.2 (by linarith : ϑ < 1)]
    have hhol : ∀ u y y', |f u x y' - f u x y| ≤ 2 * C * (1 + ‖x‖ ^ m) * ‖y' - y‖ ^ ϑ := by
      intro u y y'
      have h := (H u).2 x x y' y
      rw [norm_iFD0_sub, Real.norm_eq_abs, sub_self, norm_zero, Real.zero_rpow hδ0,
        min_eq_left zero_le_one, zero_add] at h
      have h2 : min (‖y' - y‖ ^ ϑ) 1 ≤ ‖y' - y‖ ^ ϑ := min_le_left _ _
      calc |f u x y' - f u x y| ≤ C * min (‖y' - y‖ ^ ϑ) 1 * (1 + ‖x‖ ^ m + ‖x‖ ^ m) := h
        _ ≤ C * ‖y' - y‖ ^ ϑ * (2 * (1 + ‖x‖ ^ m)) := by gcongr
        _ = 2 * C * (1 + ‖x‖ ^ m) * ‖y' - y‖ ^ ϑ := by ring
    refine ⟨fun u y => ?_, htime', fun u => continuous_of_holder hϑ.1 (hhol u),
      fun u y => ?_, fun u y y' => ?_⟩
    · have := (H u).1 x y
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    · rw [hlin, norm_zero]; positivity
    · rw [hlin]; simpa using hhol u y y'
  · -- 1 ≤ ϑ < 2
    simp only [Nat.cast_one] at hcore hk1 hk2
    have hlin : ∀ u y, lin ϑ (f u x) y = fderiv ℝ (f u x) y := fun u y => by simp [lin, hk1]
    have hdiff : ∀ u, Differentiable ℝ (f u x) := fun u =>
      diff_of_iFD0 ((hcore u).1 x 0 (by norm_num))
    have hgrowth : ∀ u y, |f u x y| ≤ C * (1 + ‖x‖ ^ m) := by
      intro u y
      have := ((hcore u).2.1 0 (by norm_num)).1 x y
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have hD : ∀ u y, ‖fderiv ℝ (f u x) y‖ ≤ C * (1 + ‖x‖ ^ m) := by
      intro u y
      rcases eq_or_ne (ϑ - 1) 0 with h0 | h0
      · have := ((hcore u).2.2.1 h0).1 x y
        rwa [norm_iteratedFDeriv_one] at this
      · have := ((hcore u).2.2.2 h0).1 x y
        rwa [norm_iteratedFDeriv_one] at this
    refine ⟨hgrowth, htime', fun u => (hdiff u).continuous, fun u y => ?_, fun u y y' => ?_⟩
    · rw [hlin]; exact hD u y
    · rw [hlin]
      rcases eq_or_ne (ϑ - 1) 0 with h0 | h0
      · have hϑ1 : ϑ = 1 := by linarith
        refine (taylor_ball (hdiff u) (B := 2 * C * (1 + ‖x‖ ^ m)) fun z _ => ?_).trans_eq ?_
        · calc ‖fderiv ℝ (f u x) z - fderiv ℝ (f u x) y‖
              ≤ ‖fderiv ℝ (f u x) z‖ + ‖fderiv ℝ (f u x) y‖ := norm_sub_le _ _
            _ ≤ C * (1 + ‖x‖ ^ m) + C * (1 + ‖x‖ ^ m) := add_le_add (hD u z) (hD u y)
            _ = 2 * C * (1 + ‖x‖ ^ m) := by ring
        · rw [hϑ1, Real.rpow_one]
      · have hpos : 0 < ϑ - 1 := lt_of_le_of_ne (by linarith) h0.symm
        refine (taylor_ball (hdiff u) (B := 2 * C * (1 + ‖x‖ ^ m) * ‖y' - y‖ ^ (ϑ - 1))
          fun z hz => ?_).trans_eq ?_
        · have h := ((hcore u).2.2.2 h0).2 x x z y
          rw [norm_iFD1_sub, sub_self, norm_zero, Real.zero_rpow hδ0,
            min_eq_left zero_le_one, zero_add] at h
          have h2 : min (‖z - y‖ ^ (ϑ - 1)) 1 ≤ ‖y' - y‖ ^ (ϑ - 1) :=
            (min_le_left _ _).trans (Real.rpow_le_rpow (norm_nonneg _) hz hpos.le)
          calc ‖fderiv ℝ (f u x) z - fderiv ℝ (f u x) y‖
              ≤ C * min (‖z - y‖ ^ (ϑ - 1)) 1 * (1 + ‖x‖ ^ m + ‖x‖ ^ m) := h
            _ ≤ C * ‖y' - y‖ ^ (ϑ - 1) * (2 * (1 + ‖x‖ ^ m)) := by gcongr
            _ = 2 * C * (1 + ‖x‖ ^ m) * ‖y' - y‖ ^ (ϑ - 1) := by ring
        · have e : ‖y' - y‖ ^ ϑ = ‖y' - y‖ ^ (ϑ - 1) * ‖y' - y‖ := by
            conv_lhs => rw [show ϑ = (ϑ - 1) + 1 by ring]
            rw [Real.rpow_add' (norm_nonneg _) (by linarith), Real.rpow_one]
          rw [e]; ring
  · -- ϑ = 2
    simp only [Nat.cast_ofNat] at hcore hk1 hk2
    have hϑ2 : ϑ = 2 := le_antisymm hϑ.2 hk1
    have hlin : ∀ u y, lin ϑ (f u x) y = fderiv ℝ (f u x) y := fun u y => by
      simp [lin, show (1:ℝ) ≤ ϑ by linarith]
    have hdiff : ∀ u, Differentiable ℝ (f u x) := fun u =>
      diff_of_iFD0 ((hcore u).1 x 0 (by norm_num))
    have hdiff2 : ∀ u, Differentiable ℝ (fderiv ℝ (f u x)) := fun u =>
      diff_of_iFD1 ((hcore u).1 x 1 (by norm_num))
    have hgrowth : ∀ u y, |f u x y| ≤ C * (1 + ‖x‖ ^ m) := by
      intro u y
      have := ((hcore u).2.1 0 (by norm_num)).1 x y
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have hD : ∀ u y, ‖fderiv ℝ (f u x) y‖ ≤ C * (1 + ‖x‖ ^ m) := by
      intro u y
      have := ((hcore u).2.1 1 (by norm_num)).1 x y
      rwa [norm_iteratedFDeriv_one] at this
    have hD2 : ∀ u y, ‖fderiv ℝ (fderiv ℝ (f u x)) y‖ ≤ C * (1 + ‖x‖ ^ m) := by
      intro u y
      have := ((hcore u).2.2.1 (by rw [hϑ2]; norm_num)).1 x y
      rwa [norm_iFD2] at this
    refine ⟨hgrowth, htime', fun u => (hdiff u).continuous, fun u y => ?_, fun u y y' => ?_⟩
    · rw [hlin]; exact hD u y
    · rw [hlin]
      refine (taylor_ball (hdiff u) (B := C * (1 + ‖x‖ ^ m) * ‖y' - y‖)
          fun z hz => ?_).trans ?_
      · have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ (f u x))
          (s := Set.univ) (x := y) (y := z) (fun w _ => hdiff2 u w) (fun w _ => hD2 u w)
          convex_univ (Set.mem_univ _) (Set.mem_univ _)
        refine h.trans ?_
        gcongr
      · rw [hϑ2, Real.rpow_two]
        have : 0 ≤ C * (1 + ‖x‖ ^ m) * ‖y' - y‖ ^ 2 := by positivity
        nlinarith

end RegF

end Moll41

open MeasureTheory Filter Topology
open scoped ContDiff

open FullyCoupledSDE.DiffApprox Moll41 in
theorem solution {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (ρ1 : ℝ → ℝ) (ρ2 : FullyCoupledSDE.Poisson.E d2 → ℝ)
    (hρ1_smooth : ContDiff ℝ ∞ ρ1) (hρ1_radial : ∀ r, ρ1 (-r) = ρ1 r)
    (hρ1_range : ∀ r, ρ1 r ∈ Set.Icc (0 : ℝ) 1) (hρ1_int : ∫ r, ρ1 r = 1)
    (hρ1_deriv : ∀ k : ℕ, 1 ≤ k → ∃ Ck > (0 : ℝ), ∀ r, |iteratedDeriv k ρ1 r| ≤ Ck * ρ1 r)
    (hρ2_smooth : ContDiff ℝ ∞ ρ2) (hρ2_radial : ∀ z z' : FullyCoupledSDE.Poisson.E d2, ‖z‖ = ‖z'‖ → ρ2 z = ρ2 z')
    (hρ2_range : ∀ z, ρ2 z ∈ Set.Icc (0 : ℝ) 1) (hρ2_int : ∫ z, ρ2 z = 1)
    (hρ2_deriv : ∀ k : ℕ, 1 ≤ k → ∃ Ck > (0 : ℝ), ∀ z, ‖iteratedFDeriv ℝ k ρ2 z‖ ≤ Ck * ρ2 z)
    (δ ϑ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hϑ : ϑ ∈ Set.Ioc (0 : ℝ) 2)
    (hρ1_mom : Integrable (fun r : ℝ => |r| ^ (ϑ / 2) * ρ1 r))
    (hρ2_mom : Integrable (fun z : FullyCoupledSDE.Poisson.E d2 => ‖z‖ ^ ϑ * ρ2 z))
    (f : ℝ → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → ℝ) (hf : CpT (ϑ / 2) δ ϑ f) :
    ∃ C0 > (0 : ℝ), ∃ m > (0 : ℝ), ∀ n : ℕ, 1 ≤ n → ∀ (t : ℝ) (x : FullyCoupledSDE.Poisson.E d1) (y : FullyCoupledSDE.Poisson.E d2),
      |f t x y - mollify ρ1 ρ2 f n t x y| ≤ C0 * (n : ℝ) ^ (-ϑ) * (1 + ‖x‖ ^ m) ∧
      DifferentiableAt ℝ (fun t' => mollify ρ1 ρ2 f n t' x y) t ∧
      ContDiff ℝ 2 (fun y' => mollify ρ1 ρ2 f n t x y') ∧
      |deriv (fun t' => mollify ρ1 ρ2 f n t' x y) t| +
          ‖iteratedFDeriv ℝ 2 (fun y' => mollify ρ1 ρ2 f n t x y') y‖ ≤
        C0 * (n : ℝ) ^ (2 - ϑ) * (1 + ‖x‖ ^ m) := by
  have hρ1i : Integrable ρ1 := Integrable.of_integral_ne_zero (by rw [hρ1_int]; norm_num)
  have hρ2i : Integrable ρ2 := Integrable.of_integral_ne_zero (by rw [hρ2_int]; norm_num)
  obtain ⟨A1, hA1, hA1b⟩ := hρ1_deriv 1 le_rfl
  obtain ⟨A2, hA2, hA2b⟩ := hρ1_deriv 2 (by norm_num)
  obtain ⟨B1, hB1, hB1b⟩ := hρ2_deriv 1 le_rfl
  obtain ⟨B2, hB2, hB2b⟩ := hρ2_deriv 2 (by norm_num)
  have base1 : Base volume ρ1 A1 A2 :=
    { cd := hρ1_smooth.of_le (WithTop.coe_le_coe.2 le_top)
      nonneg := fun r => (hρ1_range r).1
      int := hρ1i
      A1_nonneg := hA1.le
      A2_nonneg := hA2.le
      d1 := fun r => by
        rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          Real.norm_eq_abs]
        exact hA1b r
      d2 := fun r => by
        rw [← norm_iFD2, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        exact hA2b r }
  have base2 : Base volume ρ2 B1 B2 :=
    { cd := hρ2_smooth.of_le (WithTop.coe_le_coe.2 le_top)
      nonneg := fun z => (hρ2_range z).1
      int := hρ2i
      A1_nonneg := hB1.le
      A2_nonneg := hB2.le
      d1 := fun z => by rw [← norm_iteratedFDeriv_one]; exact hB1b z
      d2 := fun z => by rw [← norm_iFD2]; exact hB2b z }
  have hev2 : ∀ z, ρ2 (-z) = ρ2 z := fun z => hρ2_radial _ _ (norm_neg z)
  set M1 := ∫ r, |r| ^ (ϑ / 2) * ρ1 r with hM1def
  set M2 := ∫ z, ‖z‖ ^ ϑ * ρ2 z with hM2def
  have hM1 : 0 ≤ M1 := integral_nonneg fun r => mul_nonneg (by positivity) (hρ1_range r).1
  have hM2 : 0 ≤ M2 := integral_nonneg fun z => mul_nonneg (by positivity) (hρ2_range z).1
  obtain ⟨C, hC, m, hm, hreg⟩ := reg_of_CpT hδ hϑ hf
  refine ⟨C * (2 * M2 + M1) + C * (A1 * M1 + 2 * B2 * M2) + 1, by positivity, m, hm, ?_⟩
  intro n hn t x y
  obtain ⟨hgr, htime, hcont, hlinb, htay⟩ := hreg x
  set W := 1 + ‖x‖ ^ m with hWdef
  have hW : 0 < W := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set K := sc ρ2 (n : ℝ) with hKdef
  set k1 := sc ρ1 ((n : ℝ) ^ 2) with hk1def
  have hK : Ker2 volume K (B1 * n) (B2 * (n : ℝ) ^ 2) := base2.ker2 hnpos
  have hk : Ker2 volume k1 (A1 * (n : ℝ) ^ 2) (A2 * ((n : ℝ) ^ 2) ^ 2) :=
    base1.ker2 (by positivity)
  have hK1 : ∫ z, K z = 1 := by rw [hKdef, integral_sc _ hnpos, hρ2_int]
  have hk1 : ∫ r, k1 r = 1 := by rw [hk1def, integral_sc _ (by positivity), hρ1_int]
  have hKev : ∀ z, K (-z) = K z := sc_even hev2 _
  have hnϑ : ((n : ℝ) ^ 2) ^ (-(ϑ / 2)) = (n : ℝ) ^ (-ϑ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    congr 1; push_cast; ring
  have hKmom : ∫ z, ‖z‖ ^ ϑ * K z = (n : ℝ) ^ (-ϑ) * M2 := moment_sc ρ2 hnpos ϑ
  have hKmomi : Integrable (fun z => ‖z‖ ^ ϑ * K z) := moment_sc_int hnpos hρ2_mom
  have hkmom : ∫ r, ‖r‖ ^ (ϑ / 2) * k1 r = (n : ℝ) ^ (-ϑ) * M1 := by
    rw [hk1def, moment_sc ρ1 (by positivity), hnϑ]
    simp only [Real.norm_eq_abs, hM1def]
  have hkmomi : Integrable (fun r => ‖r‖ ^ (ϑ / 2) * k1 r) :=
    moment_sc_int (by positivity) (by simpa only [Real.norm_eq_abs] using hρ1_mom)
  have hk0 : ∀ r, 0 ≤ k1 r := hk.nonneg
  have hKlin : ∀ u y', lin ϑ (f u x) y' = 0 ∨ Integrable (fun z => ‖z‖ * K z) := by
    intro u y'
    by_cases h1 : 1 ≤ ϑ
    · right
      refine (hK.int.add hKmomi).mono'
        (continuous_norm.mul hK.diff.continuous).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hK.nonneg z))]
      have : ‖z‖ ≤ 1 + ‖z‖ ^ ϑ := by
        rcases le_total ‖z‖ 1 with hz | hz
        · linarith [Real.rpow_nonneg (norm_nonneg z) ϑ]
        · linarith [Real.self_le_rpow_of_one_le hz h1]
      show ‖z‖ * K z ≤ K z + ‖z‖ ^ ϑ * K z
      nlinarith [hK.nonneg z]
    · left; simp [lin, h1]
  -- identification of the kernels
  have hKid : ∀ z, rho2n ρ2 n z = K z := by
    intro z; simp [rho2n, hKdef, sc, finrank_euclideanSpace_fin]
  have hkid : ∀ r, rho1n ρ1 n r = k1 r := by
    intro r; simp [rho1n, hk1def, sc, Module.finrank_self, smul_eq_mul]
  set Sy : ℝ → FullyCoupledSDE.Poisson.E d2 → ℝ := fun u y => ∫ w, f u x w * K (y - w) with hSy
  have hR1 : ∀ t' y', mollify ρ1 ρ2 f n t' x y' = ∫ s, Sy (t' - s) y' * k1 s := by
    intro t' y'
    simp only [mollify, hKid, hkid, hSy]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    rw [integral_mul_const]
    congr 1
    rw [← integral_sub_left_eq_self (fun z => f (t' - s) x (y' - z) * K z) volume y']
    simp only [sub_sub_cancel]
  have hR2 : ∀ t' y', mollify ρ1 ρ2 f n t' x y' = ∫ u, Sy u y' * k1 (t' - u) := by
    intro t' y'
    rw [hR1, ← integral_sub_left_eq_self (fun s => Sy (t' - s) y' * k1 s) volume t']
    simp only [sub_sub_cancel]
  -- continuity in time
  have hcu : ∀ w, Continuous fun u => f u x w := by
    intro w
    refine continuous_of_holder (E := ℝ) (L := C * W) (a := ϑ / 2) (by linarith [hϑ.1])
      fun u u' => ?_
    have := htime u' u w
    rw [Real.norm_eq_abs]
    linarith
  have hKc : Continuous K := hK.diff.continuous
  -- properties of the spatial smoothing
  have hSyb : ∀ u y', |Sy u y'| ≤ C * W := by
    intro u y'
    have h := crude_bound (μ := volume) hK.toKer (V := ℝ) (D := K) (a := 1)
      (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hK.nonneg z), one_mul]) (hgr u) y'
    rw [hK1] at h
    simpa [hSy, smul_eq_mul, Real.norm_eq_abs] using h
  have hSyt : ∀ u u' y', |Sy u y' - Sy u' y'| ≤ C * W * |u - u'| ^ (ϑ / 2) := by
    intro u u' y'
    have hi : ∀ v, Integrable (fun w => f v x w * K (y' - w)) := fun v =>
      ((hK.int.comp_sub_left y').const_mul (C * W)).mono'
        (((hcont v).mul (hKc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
        (Eventually.of_forall fun w => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hK.nonneg _)]
          exact mul_le_mul_of_nonneg_right (hgr v w) (hK.nonneg _))
    have e : Sy u y' - Sy u' y' = ∫ w, (f u x w - f u' x w) * K (y' - w) := by
      simp only [hSy, sub_mul]
      rw [integral_sub (hi u) (hi u')]
    rw [e, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le ((hK.int.comp_sub_left y').const_mul
      (C * W * |u - u'| ^ (ϑ / 2))) (Eventually.of_forall fun w => ?_)).trans_eq ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hK.nonneg _)]
      refine mul_le_mul_of_nonneg_right ?_ (hK.nonneg _)
      have := htime u u' w
      linarith
    · rw [integral_const_mul, integral_sub_left_eq_self K volume y', hK1, mul_one]
  have hSyc : ∀ y', Continuous fun u => Sy u y' := by
    intro y'
    have h := cont_param (μ := volume) hK.toKer (V := ℝ) (D := K) hKc (a := 1)
      (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hK.nonneg z), one_mul])
      (G := fun u w => f u x w) hcu hcont (hgr) y'
    simpa [hSy, smul_eq_mul] using h
  have hkmomi' : Integrable (fun s : ℝ => |s| ^ (ϑ / 2) * k1 s) := by
    simpa only [Real.norm_eq_abs] using hkmomi
  have hkmom' : ∫ s : ℝ, |s| ^ (ϑ / 2) * k1 s = (n : ℝ) ^ (-ϑ) * M1 := by
    simpa only [Real.norm_eq_abs] using hkmom
  have hnϑ0 : 0 ≤ (n : ℝ) ^ (-ϑ) := by positivity
  -- (A) the approximation bound
  have hA : |f t x y - mollify ρ1 ρ2 f n t x y| ≤
      C * (2 * M2 + M1) * (n : ℝ) ^ (-ϑ) * W := by
    rw [hR1, abs_sub_comm]
    have hpt : ∀ s, |Sy (t - s) y - f t x y| ≤
        2 * C * W * ((n : ℝ) ^ (-ϑ) * M2) + C * W * |s| ^ (ϑ / 2) := by
      intro s
      have h1 := abs_S_sub_le (μ := volume) hK.toKer hKev hK1 (g := f (t - s) x)
        (hcont _).aestronglyMeasurable (hgr (t - s)) (y := y) (L := 2 * C * W) (p := ϑ)
        (lin ϑ (f (t - s) x) y) (hKlin (t - s) y) (fun w => htay (t - s) y w) hKmomi
      rw [hKmom] at h1
      have h2 := htime (t - s) t y
      have e : |t - s - t| = |s| := by rw [show t - s - t = -s by ring, abs_neg]
      rw [e] at h2
      calc |Sy (t - s) y - f t x y|
          ≤ |Sy (t - s) y - f (t - s) x y| + |f (t - s) x y - f t x y| := abs_sub_le _ _ _
        _ ≤ 2 * C * W * ((n : ℝ) ^ (-ϑ) * M2) + C * W * |s| ^ (ϑ / 2) := by
          refine add_le_add h1 ?_
          linarith
    have h := avg_bound hk0 hk.int hk1
      ((hSyc y).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (M := C * W) (fun s => hSyb _ _) (c := f t x y) hkmomi' hpt
    rw [hkmom'] at h
    refine h.trans_eq ?_
    ring
  -- (B) the time derivative
  have hS1 := hasFDerivAt_S (μ := volume) hk.toKer (g := fun u => Sy u y)
    ((hSyc y).aestronglyMeasurable) (M := C * W) (fun u => hSyb u y) t
  have hfun : (fun t' => mollify ρ1 ρ2 f n t' x y) = fun t' => ∫ u, Sy u y * k1 (t' - u) :=
    funext fun t' => hR2 t' y
  have hderiv : HasDerivAt (fun t' => mollify ρ1 ρ2 f n t' x y)
      ((∫ u, Sy u y • fderiv ℝ k1 (t - u)) 1) t := by
    rw [hfun]; exact hS1.hasDerivAt
  have hBb : |deriv (fun t' => mollify ρ1 ρ2 f n t' x y) t| ≤
      C * W * (A1 * (n : ℝ) ^ 2) * ((n : ℝ) ^ (-ϑ) * M1) := by
    rw [hderiv.deriv]
    have h1 := norm_S1_le (μ := volume) hk.toKer (g := fun u => Sy u y)
      (hSyc y).aestronglyMeasurable (fun u => hSyb u y) (y := t) (L := C * W) (p := ϑ / 2)
      (fun w => by rw [Real.norm_eq_abs]; exact hSyt w t y) hkmomi
    rw [hkmom] at h1
    refine le_trans ?_ h1
    have := (∫ u, Sy u y • fderiv ℝ k1 (t - u)).le_opNorm 1
    rw [Real.norm_eq_abs, norm_one, mul_one] at this
    exact this
  -- (C), (D) the space derivatives
  have hout := outer_C2 (E := FullyCoupledSDE.Poisson.E d2) hk.int hk0
    (Ψ := fun s y' => Sy (t - s) y')
    (Ψ1 := fun s y' => ∫ w, f (t - s) x w • fderiv ℝ K (y' - w))
    (Ψ2 := fun s y' => ∫ w, f (t - s) x w • fderiv ℝ (fderiv ℝ K) (y' - w))
    (fun s y' => hasFDerivAt_S (μ := volume) hK.toKer (hcont (t - s)).aestronglyMeasurable
      (hgr (t - s)) y')
    (fun s y' => hasFDerivAt_S1 hK (hcont (t - s)).aestronglyMeasurable (hgr (t - s)) y')
    (fun s => continuous_S2 hK (hcont (t - s)).aestronglyMeasurable (hgr (t - s)))
    (fun y' => ((hSyc y').comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (fun y' => ((cont_param hK.toKer hK.cont_fderiv hK.d1 (G := fun u w => f u x w) hcu hcont
      hgr y').comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (fun y' => ((cont_param hK.toKer hK.cont_fderiv2 hK.d2 (G := fun u w => f u x w) hcu hcont
      hgr y').comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (B0 := C * W) (B1 := C * W * (B1 * n) * 1)
    (B2 := 2 * C * W * (B2 * (n : ℝ) ^ 2) * ((n : ℝ) ^ (-ϑ) * M2))
    (fun s y' => hSyb _ _)
    (fun s y' => by
      have := crude_bound (μ := volume) hK.toKer hK.d1 (hgr (t - s)) y'
      rwa [hK1] at this)
    (fun s y' => by
      have := norm_S2_le (μ := volume) hK hKev (hcont (t - s)).aestronglyMeasurable
        (hgr (t - s)) (y := y') (lin ϑ (f (t - s) x) y') (hKlin (t - s) y') (htay (t - s) y')
        hKmomi
      rwa [hKmom] at this)
  have hfun2 : (fun y' => mollify ρ1 ρ2 f n t x y') = fun y' => ∫ s, Sy (t - s) y' * k1 s :=
    funext fun y' => hR1 t y'
  have hpow : (n : ℝ) ^ 2 * (n : ℝ) ^ (-ϑ) = (n : ℝ) ^ (2 - ϑ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]; ring_nf
  have hC0 : 0 ≤ C * (A1 * M1 + 2 * B2 * M2) := by positivity
  refine ⟨?_, hderiv.differentiableAt, ?_, ?_⟩
  · refine hA.trans ?_
    have : C * (2 * M2 + M1) ≤ C * (2 * M2 + M1) + C * (A1 * M1 + 2 * B2 * M2) + 1 := by
      linarith
    have hnW : 0 ≤ (n : ℝ) ^ (-ϑ) * W := by positivity
    calc C * (2 * M2 + M1) * (n : ℝ) ^ (-ϑ) * W
        = C * (2 * M2 + M1) * ((n : ℝ) ^ (-ϑ) * W) := by ring
      _ ≤ (C * (2 * M2 + M1) + C * (A1 * M1 + 2 * B2 * M2) + 1) * ((n : ℝ) ^ (-ϑ) * W) :=
          mul_le_mul_of_nonneg_right this hnW
      _ = _ := by ring
  · rw [hfun2]; exact hout.1
  · rw [hfun2, norm_iFD2]
    have h2 := hout.2 y
    rw [hk1, mul_one] at h2
    have hsum : |deriv (fun t' => mollify ρ1 ρ2 f n t' x y) t| +
        ‖fderiv ℝ (fderiv ℝ fun y' => ∫ s, Sy (t - s) y' * k1 s) y‖ ≤
        C * (A1 * M1 + 2 * B2 * M2) * (n : ℝ) ^ (2 - ϑ) * W := by
      rw [← hpow]
      calc _ ≤ C * W * (A1 * (n : ℝ) ^ 2) * ((n : ℝ) ^ (-ϑ) * M1) +
            2 * C * W * (B2 * (n : ℝ) ^ 2) * ((n : ℝ) ^ (-ϑ) * M2) := add_le_add hBb h2
        _ = _ := by ring
    refine hsum.trans ?_
    have : C * (A1 * M1 + 2 * B2 * M2) ≤
        C * (2 * M2 + M1) + C * (A1 * M1 + 2 * B2 * M2) + 1 := by
      have : 0 ≤ C * (2 * M2 + M1) := by positivity
      linarith
    have hnW : 0 ≤ (n : ℝ) ^ (2 - ϑ) * W := by positivity
    calc C * (A1 * M1 + 2 * B2 * M2) * (n : ℝ) ^ (2 - ϑ) * W
        = C * (A1 * M1 + 2 * B2 * M2) * ((n : ℝ) ^ (2 - ϑ) * W) := by ring
      _ ≤ (C * (2 * M2 + M1) + C * (A1 * M1 + 2 * B2 * M2) + 1) * ((n : ℝ) ^ (2 - ϑ) * W) :=
          mul_le_mul_of_nonneg_right this hnW
      _ = _ := by ring
