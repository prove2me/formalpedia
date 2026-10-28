-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_fderiv_kernel_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:24:58.804288+00:00
-- url     : https://prove2.me/submissions/973f22d8-1b66-4951-9e1b-652bd6a36ca2

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section LipschitzConvolution
open MeasureTheory
open scoped Convolution
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
 theorem solution
    {F : E → E} {G : NNReal} (hF : LipschitzWith G F)
    (k : E → ℝ) (hk : ContDiff ℝ 1 k) (hc : HasCompactSupport k)
    (x v : E) (ℓ : E →L[ℝ] ℝ) :
    (∫ t, fderiv ℝ k t v * ℓ (F (x - t))) =
      ∫ t, k t * ℓ (fderiv ℝ F (x - t) v) := by
  let g : E → ℝ := fun y => k (x - y)
  have hgc : HasCompactSupport g :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  have hgd : ContDiff ℝ 1 g :=
    hk.comp (contDiff_const.sub contDiff_id)
  obtain ⟨D, hg⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hgc hgd (by decide)
  have hdg (y : E) :
      lineDeriv ℝ g y (-v) = fderiv ℝ k (x - y) v := by
    change lineDeriv ℝ (k ∘ (fun z : E => x - z)) y (-v) = _
    simpa only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, neg_neg] using
      ((((hk.differentiable (by decide)) (x - y)).hasFDerivAt.comp y
        ((hasFDerivAt_id (𝕜 := ℝ) y).const_sub x)).hasLineDerivAt (-v)).lineDeriv
  have hdF :
      ∀ᵐ y ∂(volume : Measure E),
        lineDeriv ℝ (ℓ ∘ F) y v = ℓ (fderiv ℝ F y v) := by
    filter_upwards [hF.ae_differentiableAt (μ := (volume : Measure E))] with y hy
    exact ((ℓ.hasFDerivAt.comp y hy.hasFDerivAt).hasLineDerivAt v).lineDeriv
  have hb :=
    (ℓ.lipschitz.comp hF).integral_lineDeriv_mul_eq
      (μ := (volume : Measure E)) hg hgc v
  have he :
      (∫ y, lineDeriv ℝ (ℓ ∘ F) y v * g y) =
        ∫ y, k (x - y) * ℓ (fderiv ℝ F y v) := by
    apply integral_congr_ae
    filter_upwards [hdF] with y hy
    rw [hy]
    exact mul_comm _ _
  rw [he] at hb
  have hb' :
      (∫ y, fderiv ℝ k (x - y) v * ℓ (F y)) =
        ∫ y, k (x - y) * ℓ (fderiv ℝ F y v) := by
    simpa only [hdg, Function.comp_apply] using hb.symm
  have ha :
      (∫ y, fderiv ℝ k (x - y) v * ℓ (F y)) =
        ∫ t, fderiv ℝ k t v * ℓ (F (x - t)) := by
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self
        (fun t => fderiv ℝ k t v * ℓ (F (x - t)))
        (volume : Measure E) x
  have hz :
      (∫ y, k (x - y) * ℓ (fderiv ℝ F y v)) =
        ∫ t, k t * ℓ (fderiv ℝ F (x - t) v) := by
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self
        (fun t => k t * ℓ (fderiv ℝ F (x - t) v))
        (volume : Measure E) x
  exact ha.symm.trans (hb'.trans hz)
