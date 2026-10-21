-- Prove2me | solution 1 for EndToEndRisk.SquaredLoss.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:47:40.508703+00:00
-- url     : https://prove2.me/submissions/16825882-2475-4303-a3b3-1d5023992af9

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
open EndToEndRisk.SquaredLoss

namespace E2ECor3Aux

variable {m : ℕ}


lemma optVal_eq (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (c : (EuclideanSpace ℝ (Fin m))) : optVal X f c = f (xstar c) + ⟪c, xstar c⟫_ℝ := by
  unfold optVal
  apply IsLeast.csInf_eq
  refine ⟨⟨xstar c, (hx c).1, rfl⟩, ?_⟩
  rintro _ ⟨x, hxX, rfl⟩
  exact (hx c).2 x hxX

lemma trueLoss_eq (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (d c : (EuclideanSpace ℝ (Fin m))) : trueLoss X f xstar d c =
      f (xstar d) + ⟪c, xstar d⟫_ℝ - (f (xstar c) + ⟪c, xstar c⟫_ℝ) := by
  unfold trueLoss; rw [optVal_eq X f xstar hx]

lemma trueLoss_nonneg (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (d c : (EuclideanSpace ℝ (Fin m))) : 0 ≤ trueLoss X f xstar d c := by
  rw [trueLoss_eq X f xstar hx]
  have := (hx c).2 (xstar d) (hx d).1
  linarith

/-- The conditional excess true loss `Δ(d, e) = f(x*(d)) − f(x*(e)) + eᵀ(x*(d) − x*(e))`. -/
noncomputable def gap (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (d e : (EuclideanSpace ℝ (Fin m))) : ℝ :=
  f (xstar d) - f (xstar e) + ⟪e, xstar d - xstar e⟫_ℝ

lemma gap_nonneg (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (d e : (EuclideanSpace ℝ (Fin m))) : 0 ≤ gap f xstar d e := by
  unfold gap
  have := (hx e).2 (xstar d) (hx d).1
  rw [inner_sub_right]
  linarith

/-- Lemma 5 / Theorem 4 of the paper: `Δ(d, e) ≤ ‖d − e‖ ‖x*(d) − x*(e)‖ ≤ B_X ‖d − e‖`. -/
lemma gap_le (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m))) (hx : IsArgminSelection X f xstar)
    (hXb : Bornology.IsBounded X) (d e : (EuclideanSpace ℝ (Fin m))) :
    gap f xstar d e ≤ Metric.diam X * ‖d - e‖ := by
  unfold gap
  have h1 := (hx d).2 (xstar e) (hx e).1
  have h2 : f (xstar d) - f (xstar e) + ⟪e, xstar d - xstar e⟫_ℝ ≤
      ⟪d - e, xstar e - xstar d⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right] at *
    linarith
  have h3 : ⟪d - e, xstar e - xstar d⟫_ℝ ≤ ‖d - e‖ * ‖xstar e - xstar d‖ :=
    real_inner_le_norm _ _
  have h4 : ‖xstar e - xstar d‖ ≤ Metric.diam X := by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hXb (hx e).1 (hx d).1
  have h5 : ‖d - e‖ * ‖xstar e - xstar d‖ ≤ ‖d - e‖ * Metric.diam X :=
    mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
  linarith

lemma measurable_f_xstar (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ) (hS : Standing X f) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)))
    (hx : IsArgminSelection X f xstar) (hxm : Measurable xstar) :
    Measurable (fun d => f (xstar d)) := by
  have hc : Continuous (X.domRestrict f) := hS.2.2.2.2.domRestrict
  have hm : Measurable (fun d => (⟨xstar d, (hx d).1⟩ : X)) := hxm.subtype_mk
  exact hc.measurable.comp hm


lemma optVal_continuous (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (hS : Standing X f) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)))
    (hx : IsArgminSelection X f xstar) : Continuous (fun c => optVal X f c) := by
  obtain ⟨R, hR⟩ := hS.2.1.isBounded.exists_norm_le
  obtain ⟨x0, hx0⟩ := hS.2.2.1
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR x0 hx0)
  refine (LipschitzWith.of_le_add_mul (Real.toNNReal R) fun c c' => ?_).continuous
  rw [optVal_eq X f xstar hx, optVal_eq X f xstar hx, Real.coe_toNNReal R hR0, dist_eq_norm]
  have h1 := (hx c).2 (xstar c') (hx c').1
  have h2 : ⟪c - c', xstar c'⟫_ℝ ≤ ‖c - c'‖ * ‖xstar c'‖ := real_inner_le_norm _ _
  have h3 := hR _ (hx c').1
  have h4 : ‖c - c'‖ * ‖xstar c'‖ ≤ R * ‖c - c'‖ := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  rw [inner_sub_left] at h2
  linarith

section Measure

variable (ν : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure ν]

lemma integrable_sq (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => ‖c‖ ^ 2) ν := by
  refine ⟨(continuous_norm.pow 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simpa [enorm_pow] using h2

lemma integrable_id' (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => c) ν := by
  refine Integrable.mono' ((integrable_const (1:ℝ)).add (integrable_sq ν h2))
    aestronglyMeasurable_id (Filter.Eventually.of_forall ?_)
  intro c
  have := norm_nonneg c
  simp only [Pi.add_apply]
  nlinarith

lemma key (u v : (EuclideanSpace ℝ (Fin m)) → ℝ) (K : ℝ) (w : (EuclideanSpace ℝ (Fin m))) (hu : Integrable u ν) (hv : Integrable v ν)
    (hid : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => c) ν) (hK : 0 ≤ K) (hu0 : ∀ c, 0 ≤ u c) (hv0 : ∀ c, 0 ≤ v c)
    (h : ∀ c, u c = K + v c + ⟪c - ∫ c, c ∂ν, w⟫_ℝ) :
    ∫⁻ c, ENNReal.ofReal (u c) ∂ν = ENNReal.ofReal K + ∫⁻ c, ENNReal.ofReal (v c) ∂ν := by
  rw [← ofReal_integral_eq_lintegral_ofReal hu (Filter.Eventually.of_forall hu0),
    ← ofReal_integral_eq_lintegral_ofReal hv (Filter.Eventually.of_forall hv0),
    ← ENNReal.ofReal_add hK (integral_nonneg hv0)]
  congr 1
  have hi : Integrable (fun c => ⟪c - ∫ c, c ∂ν, w⟫_ℝ) ν := by
    have : Integrable (fun c => c - ∫ c, c ∂ν) ν := hid.sub (integrable_const _)
    simpa [real_inner_comm] using this.inner_const (𝕜 := ℝ) w
  have h0 : ∫ c, ⟪c - ∫ c, c ∂ν, w⟫_ℝ ∂ν = 0 := by
    have e1 : ∀ c, ⟪c - ∫ c, c ∂ν, w⟫_ℝ = ⟪w, c - ∫ c, c ∂ν⟫_ℝ := fun c => real_inner_comm _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall e1),
      integral_inner (f := fun c => c - ∫ c, c ∂ν) (hid.sub (integrable_const _)) w,
      integral_sub hid (integrable_const _)]
    simp
  rw [integral_congr_ae (Filter.Eventually.of_forall h),
    integral_add (f := fun c => K + v c) ((integrable_const K).add hv) hi,
    integral_add (integrable_const K) hv, h0]
  simp


lemma integrable_sq_sub (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) (a : (EuclideanSpace ℝ (Fin m))) :
    Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => ‖a - c‖ ^ 2) ν := by
  refine Integrable.mono' ((integrable_const (2 * ‖a‖ ^ 2)).add
    ((integrable_sq ν h2).const_mul 2))
    ((continuous_const.sub continuous_id).norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro c
  have h1 := norm_sub_le a c
  have := norm_nonneg a
  have := norm_nonneg c
  have := norm_nonneg (a - c)
  simp only [Pi.add_apply, norm_pow, norm_norm]
  nlinarith [mul_self_le_mul_self this h1, sq_nonneg (‖a‖ - ‖c‖)]

/-- Conditional decomposition of the squared loss:
`E‖d − c‖² = ‖d − c̄‖² + E‖c̄ − c‖²` with `c̄ = E c`. -/
lemma cond_ls (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) (d : (EuclideanSpace ℝ (Fin m))) :
    ∫⁻ c, ENNReal.ofReal (lsLoss d c) ∂ν =
      ENNReal.ofReal (‖d - ∫ c, c ∂ν‖ ^ 2) +
        ∫⁻ c, ENNReal.ofReal (lsLoss (∫ c, c ∂ν) c) ∂ν := by
  unfold lsLoss
  refine key ν _ _ _ ((-2 : ℝ) • (d - ∫ c, c ∂ν)) (integrable_sq_sub ν h2 d)
    (integrable_sq_sub ν h2 _) (integrable_id' ν h2) (sq_nonneg _) (fun _ => sq_nonneg _)
    (fun _ => sq_nonneg _) ?_
  intro c
  have : d - c = (d - ∫ c, c ∂ν) + ((∫ c, c ∂ν) - c) := by abel
  rw [this, norm_add_sq_real, inner_smul_right, real_inner_comm]
  have : c - ∫ c, c ∂ν = -((∫ c, c ∂ν) - c) := by abel
  rw [this, inner_neg_left]
  ring

lemma integrable_trueLoss (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (hS : Standing X f) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)))
    (hx : IsArgminSelection X f xstar)
    (hid : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => c) ν) (e : (EuclideanSpace ℝ (Fin m))) :
    Integrable (fun c => trueLoss X f xstar e c) ν := by
  obtain ⟨K, hK⟩ := hS.2.1.exists_bound_of_continuousOn hS.2.2.2.2
  obtain ⟨R, hR⟩ := hS.2.1.isBounded.exists_norm_le
  have i1 : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => ⟪c, xstar e⟫_ℝ) ν :=
    hid.inner_const (xstar e)
  have i2 : Integrable (fun c => optVal X f c) ν := by
    refine Integrable.mono' ((integrable_const K).add (hid.norm.const_mul R))
      (optVal_continuous X f hS xstar hx).aestronglyMeasurable
      (Filter.Eventually.of_forall ?_)
    intro c
    rw [optVal_eq X f xstar hx, Real.norm_eq_abs]
    have h1 : |⟪c, xstar c⟫_ℝ| ≤ ‖c‖ * ‖xstar c‖ := abs_real_inner_le_norm _ _
    have h3 := hR _ (hx c).1
    have h4 := hK _ (hx c).1
    rw [Real.norm_eq_abs] at h4
    have := norm_nonneg c
    simp only [Pi.add_apply]
    have h5 : ‖c‖ * ‖xstar c‖ ≤ R * ‖c‖ := by nlinarith
    calc |f (xstar c) + ⟪c, xstar c⟫_ℝ| ≤ |f (xstar c)| + |⟪c, xstar c⟫_ℝ| := abs_add_le _ _
      _ ≤ K + R * ‖c‖ := by linarith
  exact ((integrable_const _).add i1).sub i2

/-- Conditional decomposition of the optimality-gap loss:
`E L(d, c) = Δ(d, c̄) + E L(c̄, c)` with `c̄ = E c`. -/
lemma cond_true (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (hS : Standing X f) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)))
    (hx : IsArgminSelection X f xstar)
    (hid : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => c) ν) (d : (EuclideanSpace ℝ (Fin m))) :
    ∫⁻ c, ENNReal.ofReal (trueLoss X f xstar d c) ∂ν =
      ENNReal.ofReal (gap f xstar d (∫ c, c ∂ν)) +
        ∫⁻ c, ENNReal.ofReal (trueLoss X f xstar (∫ c, c ∂ν) c) ∂ν := by
  have hint := integrable_trueLoss ν X f hS xstar hx hid
  refine key ν _ _ _ (xstar d - xstar (∫ c, c ∂ν)) (hint d) (hint _) hid
    (gap_nonneg X f xstar hx _ _) (trueLoss_nonneg X f xstar hx d)
    (trueLoss_nonneg X f xstar hx _) ?_
  intro c
  rw [trueLoss_eq X f xstar hx, trueLoss_eq X f xstar hx]
  unfold gap
  simp only [inner_sub_left, inner_sub_right]
  ring

lemma condExcess_true (X : Set (EuclideanSpace ℝ (Fin m))) (f : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (hS : Standing X f) (xstar : (EuclideanSpace ℝ (Fin m)) → (EuclideanSpace ℝ (Fin m)))
    (hx : IsArgminSelection X f xstar)
    (hid : Integrable (fun c : (EuclideanSpace ℝ (Fin m)) => c) ν) (d : (EuclideanSpace ℝ (Fin m))) :
    (⨅ d', condRisk (trueLoss X f xstar) ν d') = condRisk (trueLoss X f xstar) ν (∫ c, c ∂ν) ∧
    condExcess (trueLoss X f xstar) ν d = ENNReal.ofReal (gap f xstar d (∫ c, c ∂ν)) := by
  have hc : ∀ d', condRisk (trueLoss X f xstar) ν d' =
      ENNReal.ofReal (gap f xstar d' (∫ c, c ∂ν)) + condRisk (trueLoss X f xstar) ν (∫ c, c ∂ν) :=
    fun d' => cond_true ν X f hS xstar hx hid d'
  have hinf : (⨅ d', condRisk (trueLoss X f xstar) ν d') =
      condRisk (trueLoss X f xstar) ν (∫ c, c ∂ν) := by
    refine le_antisymm (iInf_le _ _) (le_iInf fun d' => ?_)
    rw [hc d']; exact le_add_self
  refine ⟨hinf, ?_⟩
  have hfin : condRisk (trueLoss X f xstar) ν (∫ c, c ∂ν) ≠ ⊤ :=
    (integrable_trueLoss ν X f hS xstar hx hid _).lintegral_lt_top.ne
  unfold condExcess
  rw [hinf, hc d, ENNReal.add_sub_cancel_right hfin]

lemma condExcess_ls (h2 : ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤) (d : (EuclideanSpace ℝ (Fin m))) :
    (⨅ d', condRisk lsLoss ν d') = condRisk lsLoss ν (∫ c, c ∂ν) ∧
    condExcess lsLoss ν d = ENNReal.ofReal (‖d - ∫ c, c ∂ν‖ ^ 2) := by
  have hc : ∀ d', condRisk lsLoss ν d' =
      ENNReal.ofReal (‖d' - ∫ c, c ∂ν‖ ^ 2) + condRisk lsLoss ν (∫ c, c ∂ν) :=
    fun d' => cond_ls ν h2 d'
  have hinf : (⨅ d', condRisk lsLoss ν d') = condRisk lsLoss ν (∫ c, c ∂ν) := by
    refine le_antisymm (iInf_le _ _) (le_iInf fun d' => ?_)
    rw [hc d']; exact le_add_self
  refine ⟨hinf, ?_⟩
  have hfin : condRisk lsLoss ν (∫ c, c ∂ν) ≠ ⊤ :=
    (integrable_sq_sub ν h2 (∫ c, c ∂ν)).lintegral_lt_top.ne
  unfold condExcess
  rw [hinf, hc d, ENNReal.add_sub_cancel_right hfin]

end Measure

lemma sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (u : α → ℝ≥0∞) (hu : Measurable u) : (∫⁻ a, u a ∂μ) ^ 2 ≤ ∫⁻ a, u a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hu.aemeasurable
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have hB : ∫⁻ a, u a ^ (2:ℝ) ∂μ = ∫⁻ a, u a ^ 2 ∂μ := by
    refine lintegral_congr fun a => ?_
    exact ENNReal.rpow_two _
  rw [hB] at h
  have e : ((∫⁻ a, u a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ (2:ℕ) = ∫⁻ a, u a ^ 2 ∂μ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc (∫⁻ a, u a ∂μ) ^ 2 ≤ ((∫⁻ a, u a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ (2:ℕ) :=
        pow_le_pow_left₀ zero_le h 2
    _ = _ := e

end E2ECor3Aux

namespace E2ECor3Aux

lemma gap_le_B {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hS : Standing X f) (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar)
    (C : Set (EuclideanSpace ℝ (Fin m))) (hA2 : Bornology.IsBounded C)
    (d e : EuclideanSpace ℝ (Fin m)) (he : e ∈ convexHull ℝ C) :
    gap f xstar d e ≤ Bf X f + Bc C * Metric.diam X := by
  have hXb : Bornology.IsBounded X := hS.2.1.isBounded
  unfold gap
  have i1 := real_inner_le_norm e (xstar d - xstar e)
  have hBf : f (xstar d) - f (xstar e) ≤ Bf X f := by
    unfold Bf
    have hcont : ContinuousOn (fun p : (EuclideanSpace ℝ (Fin m)) × (EuclideanSpace ℝ (Fin m)) =>
        f p.1 - f p.2) (X ×ˢ X) :=
      (hS.2.2.2.2.comp continuousOn_fst (fun p hp => hp.1)).sub
        (hS.2.2.2.2.comp continuousOn_snd (fun p hp => hp.2))
    exact le_csSup ((hS.2.1.prod hS.2.1).bddAbove_image hcont)
      ⟨(xstar d, xstar e), ⟨(hx d).1, (hx _).1⟩, rfl⟩
  have hBc : ‖e‖ ≤ Bc C := by
    obtain ⟨R, hR⟩ := hA2.exists_norm_le
    have hbdd : BddAbove ((fun c => ‖c‖) '' C) := ⟨R, by rintro _ ⟨c, hc, rfl⟩; exact hR c hc⟩
    have hsub : C ⊆ Metric.closedBall 0 (Bc C) := fun c hc => by
      rw [mem_closedBall_zero_iff]; exact le_csSup hbdd ⟨c, hc, rfl⟩
    have := (convexHull_min hsub (convex_closedBall 0 _)) he
    rwa [mem_closedBall_zero_iff] at this
  have hdiam : ‖xstar d - xstar e‖ ≤ Metric.diam X := by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hXb (hx d).1 (hx _).1
  have i2 : ‖e‖ * ‖xstar d - xstar e‖ ≤ Bc C * Metric.diam X :=
    mul_le_mul hBc hdiam (norm_nonneg _) ((norm_nonneg _).trans hBc)
  linarith

end E2ECor3Aux

open E2ECor3Aux in
theorem solution {m : ℕ} {W : Type*} [MeasurableSpace W]
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar) (hxm : Measurable xstar)
    (C : Set (EuclideanSpace ℝ (Fin m))) (hA2 : Bornology.IsBounded C)
    (ℓ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hℓm : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ d c, 0 ≤ ℓ d c)
    (Q : Set (Measure (EuclideanSpace ℝ (Fin m))))
    (hQ : ∀ ν ∈ Q, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧
      Integrable (fun c => c) ν ∧
      (∫ c, c ∂ν) ∈ convexHull ℝ C)
    (hUC : UniformlyCalibrated ℓ (trueLoss X f xstar) Q) :
    (∀ ε ∈ Set.Ioc 0 (Bf X f + Bc C * Metric.diam X),
        0 < deltaBiconj (deltaL ℓ (trueLoss X f xstar) Q) (Bf X f + Bc C * Metric.diam X) ε) ∧
      ∀ (μ : Measure W) [IsProbabilityMeasure μ]
        (κ : Kernel W (EuclideanSpace ℝ (Fin m))) [IsMarkovKernel κ],
        (∀ w, κ w ∈ Q) →
        EndToEndRisk.SquaredLoss.bayesRisk ℓ (μ ⊗ₘ κ) = ∫⁻ w, ⨅ d', condRisk ℓ (κ w) d' ∂μ →
        EndToEndRisk.SquaredLoss.bayesRisk ℓ (μ ⊗ₘ κ) < ⊤ →
        ∀ g : W → EuclideanSpace ℝ (Fin m), Measurable g →
          deltaBiconj (deltaL ℓ (trueLoss X f xstar) Q) (Bf X f + Bc C * Metric.diam X)
              (risk (trueLoss X f xstar) (μ ⊗ₘ κ) g -
                EndToEndRisk.SquaredLoss.bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ)).toReal ≤
            risk ℓ (μ ⊗ₘ κ) g - EndToEndRisk.SquaredLoss.bayesRisk ℓ (μ ⊗ₘ κ) := by
  set B := Bf X f + Bc C * Metric.diam X with hB
  -- the conditional excess true risk is the explicit gap
  have hE : ∀ ν ∈ Q, ∀ d, condExcess (trueLoss X f xstar) ν d =
      ENNReal.ofReal (gap f xstar d (∫ c, c ∂ν)) := by
    intro ν hν d
    haveI := (hQ ν hν).1
    exact (condExcess_true ν X f hS xstar hx (hQ ν hν).2.2.1 d).2
  -- δ is bounded below by a positive constant beyond any positive level
  have hlow : ∀ t, ∀ r, (∀ ν ∈ Q, ∀ d, condExcess ℓ ν d < ENNReal.ofReal r →
      condExcess (trueLoss X f xstar) ν d < ENNReal.ofReal t) →
      ∀ s, t ≤ s → ENNReal.ofReal r ≤ deltaL ℓ (trueLoss X f xstar) Q s := by
    intro t r hr s hts
    unfold deltaL
    refine le_iInf₂ fun ν hν => le_iInf fun d => le_iInf fun hd => ?_
    by_contra hlt
    have h1 := hr ν hν d (not_le.mp hlt)
    have h2 : ENNReal.ofReal t ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal hts
    exact absurd (h2.trans hd) (not_le.mpr h1)
  refine ⟨?_, ?_⟩
  · rintro ε ⟨hε0, hεB⟩
    obtain ⟨r, hr0, hr⟩ := hUC (ε / 2) (by linarith)
    have hBε : 0 < B - ε / 2 := by linarith
    set a := r / (B - ε / 2) with ha
    have ha0 : 0 < a := div_pos hr0 hBε
    set h : ℝ → ℝ := fun t => max (a * (t - ε / 2)) 0 with hh
    have hconv : ConvexOn ℝ Set.univ h := by
      have h1 : ConvexOn ℝ Set.univ (fun t : ℝ => a * (t - ε / 2)) := by
        refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
        simp only [smul_eq_mul]
        have : q = 1 - p := by linarith
        subst this
        nlinarith
      exact h1.sup (convexOn_const 0 convex_univ)
    have h0 : h 0 ≤ 0 := by
      simp only [hh]
      have : a * (0 - ε / 2) ≤ 0 := by nlinarith
      exact max_le this le_rfl
    have hle : ∀ t ∈ Set.Ioc 0 B, ENNReal.ofReal (h t) ≤ deltaL ℓ (trueLoss X f xstar) Q t := by
      rintro t ⟨ht0, htB⟩
      by_cases htε : t ≤ ε / 2
      · have : a * (t - ε / 2) ≤ 0 := by nlinarith
        have : h t = 0 := max_eq_right this
        rw [this, ENNReal.ofReal_zero]
        exact zero_le
      · push_neg at htε
        refine le_trans ?_ (hlow (ε / 2) r hr t htε.le)
        apply ENNReal.ofReal_le_ofReal
        simp only [hh]
        refine max_le ?_ hr0.le
        have : a * (t - ε / 2) ≤ a * (B - ε / 2) := by nlinarith
        rw [ha, div_mul_cancel₀ _ hBε.ne'] at this
        exact this
    have hpos : 0 < ENNReal.ofReal (h ε) := by
      apply ENNReal.ofReal_pos.mpr
      simp only [hh]
      exact lt_max_of_lt_left (by nlinarith)
    refine lt_of_lt_of_le hpos ?_
    unfold deltaBiconj
    exact le_iSup_of_le h (le_iSup_of_le hconv (le_iSup_of_le h0 (le_iSup_of_le hle le_rfl)))
  · intro μ _ κ _ hκQ hbayes hfin g hg
    have hint : ∀ w, Integrable (fun c => c) (κ w) := fun w => (hQ (κ w) (hκQ w)).2.2.1
    set cbar : W → EuclideanSpace ℝ (Fin m) := fun w => ∫ c, c ∂(κ w) with hcbar
    have hcm : Measurable cbar := (stronglyMeasurable_id.integral_kernel (κ := κ)).measurable
    have hfm := measurable_f_xstar X f hS xstar hx hxm
    have hmT : ∀ h : W → EuclideanSpace ℝ (Fin m), Measurable h →
        Measurable (fun p : W × EuclideanSpace ℝ (Fin m) =>
          ENNReal.ofReal (trueLoss X f xstar (h p.1) p.2)) := by
      intro h hh
      have : (fun p : W × EuclideanSpace ℝ (Fin m) => trueLoss X f xstar (h p.1) p.2) =
          fun p => f (xstar (h p.1)) + ⟪p.2, xstar (h p.1)⟫_ℝ -
            (f (xstar p.2) + ⟪p.2, xstar p.2⟫_ℝ) := by
        funext p; exact trueLoss_eq X f xstar hx _ _
      refine ENNReal.measurable_ofReal.comp ?_
      rw [this]
      have a1 : Measurable (fun p : W × EuclideanSpace ℝ (Fin m) => xstar (h p.1)) :=
        hxm.comp (hh.comp measurable_fst)
      have a2 : Measurable (fun p : W × EuclideanSpace ℝ (Fin m) => xstar p.2) :=
        hxm.comp measurable_snd
      exact ((hfm.comp (hh.comp measurable_fst)).add (measurable_snd.inner a1)).sub
        ((hfm.comp measurable_snd).add (measurable_snd.inner a2))
    have hgapm : ∀ h : W → EuclideanSpace ℝ (Fin m), Measurable h →
        Measurable (fun w => ENNReal.ofReal (gap f xstar (h w) (cbar w))) := by
      intro h hh
      unfold gap
      exact ENNReal.measurable_ofReal.comp
        (((hfm.comp hh).sub (hfm.comp hcm)).add
          (hcm.inner ((hxm.comp hh).sub (hxm.comp hcm))))
    set mT : W → ℝ≥0∞ := fun w => ∫⁻ c, ENNReal.ofReal (trueLoss X f xstar (cbar w) c) ∂(κ w)
    have riskT : ∀ h : W → EuclideanSpace ℝ (Fin m), Measurable h →
        risk (trueLoss X f xstar) (μ ⊗ₘ κ) h =
          ∫⁻ w, ENNReal.ofReal (gap f xstar (h w) (cbar w)) ∂μ + ∫⁻ w, mT w ∂μ := by
      intro h hh
      unfold risk
      rw [Measure.lintegral_compProd (hmT h hh), ← lintegral_add_left (hgapm h hh)]
      refine lintegral_congr fun w => ?_
      exact cond_true (κ w) X f hS xstar hx (hint w) (h w)
    have hbT : ∫⁻ w, mT w ∂μ ≤ EndToEndRisk.SquaredLoss.bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ) := by
      unfold EndToEndRisk.SquaredLoss.bayesRisk
      refine le_iInf₂ fun h hh => ?_
      rw [riskT h hh]
      exact le_add_self
    -- upper bound on the Bayes squared-loss risk
    have hrc : risk (trueLoss X f xstar) (μ ⊗ₘ κ) cbar = ∫⁻ w, mT w ∂μ := by
      rw [riskT cbar hcm]; simp [gap]
    have hb : EndToEndRisk.SquaredLoss.bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ) =
        ∫⁻ w, mT w ∂μ := by
      refine le_antisymm ?_ hbT
      unfold EndToEndRisk.SquaredLoss.bayesRisk
      exact (iInf₂_le cbar hcm).trans hrc.le
    -- the surrogate side: ∫ conditional excess ≤ excess risk
    set a : W → ℝ≥0∞ := fun w => condRisk ℓ (κ w) (g w) with ha
    set b : W → ℝ≥0∞ := fun w => ⨅ d', condRisk ℓ (κ w) d' with hbdef
    have hRa : risk ℓ (μ ⊗ₘ κ) g = ∫⁻ w, a w ∂μ := by
      unfold risk
      rw [Measure.lintegral_compProd]
      · rfl
      · exact ENNReal.measurable_ofReal.comp
          (hℓm.comp ((hg.comp measurable_fst).prodMk measurable_snd))
    have hsur : ∫⁻ w, condExcess ℓ (κ w) (g w) ∂μ ≤
        risk ℓ (μ ⊗ₘ κ) g - EndToEndRisk.SquaredLoss.bayesRisk ℓ (μ ⊗ₘ κ) := by
      rw [hRa, hbayes]
      have hbfin : ∫⁻ w, b w ∂μ ≠ ⊤ := by rw [← hbayes]; exact hfin.ne
      refine ENNReal.le_sub_of_add_le_right hbfin ?_
      refine (le_lintegral_add _ _).trans (le_of_eq (lintegral_congr fun w => ?_))
      exact tsub_add_cancel_of_le (iInf_le _ _)
    -- the gap function
    set G : W → ℝ := fun w => gap f xstar (g w) (cbar w) with hG
    have hG0 : ∀ w, 0 ≤ G w := fun w => gap_nonneg X f xstar hx _ _
    have hGB : ∀ w, G w ≤ B := fun w =>
      gap_le_B X f hS xstar hx C hA2 _ _ (hQ (κ w) (hκQ w)).2.2.2
    have hGm : Measurable G := by
      unfold G gap
      exact ((hfm.comp hg).sub (hfm.comp hcm)).add
        (hcm.inner ((hxm.comp hg).sub (hxm.comp hcm)))
    have hGi : Integrable G μ :=
      Integrable.mono' (integrable_const B) hGm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hG0 w)]; exact hGB w)
    unfold deltaBiconj
    refine iSup_le fun h => iSup_le fun hconv => iSup_le fun h0 => iSup_le fun hle => ?_
    have hcont : Continuous h := by
      have := hconv.continuousOn_interior
      rw [interior_univ] at this
      exact continuousOn_univ.mp this
    -- pointwise: h(G w) ≤ conditional excess surrogate risk
    have hpt : ∀ w, ENNReal.ofReal (h (G w)) ≤ condExcess ℓ (κ w) (g w) := by
      intro w
      rcases (hG0 w).lt_or_eq with hpos | hzero
      · refine (hle (G w) ⟨hpos, hGB w⟩).trans ?_
        unfold deltaL
        refine (iInf₂_le (κ w) (hκQ w)).trans ((iInf_le _ (g w)).trans (iInf_le _ ?_))
        rw [hE (κ w) (hκQ w) (g w)]
      · rw [← hzero, ENNReal.ofReal_of_nonpos h0]
        exact zero_le
    -- Jensen
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := B)).exists_bound_of_continuousOn
      hcont.continuousOn
    have hhGi : Integrable (fun w => h (G w)) μ :=
      Integrable.mono' (integrable_const M) (hcont.measurable.comp hGm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => hM _ ⟨hG0 w, hGB w⟩)
    have hjen : h (∫ w, G w ∂μ) ≤ ∫ w, h (G w) ∂μ :=
      (hconv.subset (Set.subset_univ _) (convex_Icc 0 B)).map_integral_le
        hcont.continuousOn isClosed_Icc
        (Filter.Eventually.of_forall fun w => ⟨hG0 w, hGB w⟩) hGi hhGi
    have hjen' : ENNReal.ofReal (h (∫ w, G w ∂μ)) ≤ ∫⁻ w, condExcess ℓ (κ w) (g w) ∂μ := by
      have hpi : Integrable (fun w => max (h (G w)) 0) μ := hhGi.sup (integrable_const 0)
      calc ENNReal.ofReal (h (∫ w, G w ∂μ))
          ≤ ENNReal.ofReal (∫ w, max (h (G w)) 0 ∂μ) := by
            apply ENNReal.ofReal_le_ofReal
            exact hjen.trans (integral_mono hhGi hpi fun w => le_max_left _ _)
        _ = ∫⁻ w, ENNReal.ofReal (max (h (G w)) 0) ∂μ :=
            ofReal_integral_eq_lintegral_ofReal hpi
              (Filter.Eventually.of_forall fun w => le_max_right _ _)
        _ ≤ ∫⁻ w, condExcess ℓ (κ w) (g w) ∂μ := by
            refine lintegral_mono fun w => ?_
            rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
            exact hpt w
    refine le_trans ?_ (hjen'.trans hsur)
    -- identify the argument of h
    by_cases hTop : ∫⁻ w, mT w ∂μ = ⊤
    · have : risk (trueLoss X f xstar) (μ ⊗ₘ κ) g -
          EndToEndRisk.SquaredLoss.bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ) = 0 := by
        rw [hb, hTop]; exact tsub_eq_zero_of_le le_top
      rw [this, ENNReal.toReal_zero, ENNReal.ofReal_of_nonpos h0]
      exact zero_le
    · have : (risk (trueLoss X f xstar) (μ ⊗ₘ κ) g -
          EndToEndRisk.SquaredLoss.bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ)).toReal =
          ∫ w, G w ∂μ := by
        rw [hb, riskT g hg, ENNReal.add_sub_cancel_right hTop,
          integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0)
            hGm.aestronglyMeasurable]
      rw [this]
