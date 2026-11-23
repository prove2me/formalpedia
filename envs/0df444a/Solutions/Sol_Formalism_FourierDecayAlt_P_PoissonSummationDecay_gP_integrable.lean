-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.gP_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:44.087375+00:00
-- url     : https://prove2.me/submissions/6af136f1-4db2-457b-a1f2-d51f8c36c709

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type} [Fintype ι]
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution [MeasurableSpace V] [BorelSpace V] (π : ι → V →L[ℝ] ℂ)
    (hπ : Function.Bijective fun (c : V) (v : ι) => π v c) : Integrable (gP π) := by
  let L : V →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun v => (π v).toLinearMap
  let T : V ≃L[ℝ] (ι → ℂ) := (LinearEquiv.ofBijective L hπ).toContinuousLinearEquiv
  have h1 : Integrable (fun w : ℂ => ((1 + ‖w‖) ^ 3)⁻¹) := by
    have := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3) (by simp; norm_num)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  have hg : Integrable (fun z : ι → ℂ => ∏ v, ((1 + ‖z v‖) ^ 3)⁻¹) :=
    Integrable.fintype_prod (f := fun _ w => ((1 + ‖w‖) ^ 3)⁻¹) (μ := fun _ => volume) fun _ => h1
  haveI : (Measure.map T (volume : Measure V)).IsAddHaarMeasure := T.isAddHaarMeasure_map _
  have hmap := Measure.isAddLeftInvariant_eq_smul (Measure.map T (volume : Measure V)) (volume : Measure (ι → ℂ))
  have hg' : Integrable (fun z : ι → ℂ => ∏ v, ((1 + ‖z v‖) ^ 3)⁻¹) (Measure.map T (volume : Measure V)) := by
    rw [hmap]
    exact hg.smul_measure_nnreal
  have := (integrable_map_equiv T.toHomeomorph.toMeasurableEquiv _).mp hg'
  exact this
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
