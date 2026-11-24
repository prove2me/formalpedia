-- Prove2me | solution 1 for Formalism.H.mFourierCoeff_torusFunC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:19.297859+00:00
-- url     : https://prove2.me/submissions/b660e616-cc86-4f9d-8116-cb241ea2a475

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_InnerDualVecBasis
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap
import Theorems.Thm_Formalism_H_mFourier_torusProj
import Theorems.Thm_Formalism_H_boxIoc_ae_eq
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
open MeasureTheory Set Complex
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.H
theorem _root_.solution (e : Module.Basis ι ℝ V) (G : V → ℂ) (hG : Continuous G)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (torusFunC e G hG hper) m =
      ∫ t in boxIco ι, G (e.equivFunL.symm t) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ))) := by
  have hS : (Set.univ.pi fun _ : ι => Ioc (0 : ℝ) (0 + 1)) =
      {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    ext x
    simp [Set.mem_univ_pi]
  have hmp : MeasurePreserving (torusProj ι)
      (volume.restrict {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)})
      (@volume (UnitAddTorus ι)
        (@MeasureSpace.pi ι _ (fun _ => UnitAddCircle) fun _ => instMeasureSpaceUnitAddCircle)) := by
    have hvol : @volume UnitAddCircle instMeasureSpaceUnitAddCircle =
        @volume UnitAddCircle (AddCircle.measureSpace 1) := by
      first
      | rfl
      | (rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; rfl)
      | (simp [AddCircle.volume_eq_smul_haarAddCircle])
      | (rw [AddCircle.volume_eq_smul_haarAddCircle]; simp)
    rw [← hS]
    show MeasurePreserving _ ((Measure.pi fun _ => volume).restrict _)
      (Measure.pi fun _ => @volume UnitAddCircle instMeasureSpaceUnitAddCircle)
    rw [Measure.restrict_pi_pi, hvol]
    exact measurePreserving_pi (μ := fun _ => volume.restrict (Ioc (0 : ℝ) (0 + 1)))
      (ν := fun _ => @volume UnitAddCircle (AddCircle.measureSpace 1))
      (fun _ => AddCircle.measurePreserving_mk 1 0)
  have hneg : dualVec e (-m) = -dualVec e m := by
    simp only [dualVec, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  have hmap := integral_map (f := fun θ => UnitAddTorus.mFourier (-m) θ • torusFunC e G hG hper θ)
    hmp.aemeasurable
    ((UnitAddTorus.mFourier (-m)).continuous.smul (torusFunC e G hG hper).continuous).aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  rw [UnitAddTorus.mFourierCoeff]
  refine hmap.trans ?_
  rw [Measure.restrict_congr_set boxIoc_ae_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show UnitAddTorus.mFourier (-m) (torusProj ι t) * torusFun e G (torusProj ι t) = _
  rw [torusFun_proj e G hper, mFourier_torusProj e (-m) t, mul_comm, hneg, inner_neg_left]
  congr 1
  push_cast
  ring
  all_goals first | infer_instance | assumption
end Formalism.H
