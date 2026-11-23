-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.isoZZ_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:35.699183+00:00
-- url     : https://prove2.me/submissions/91b83f1f-f017-4219-a71d-4c0f6dff8bbb

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {n n' n'' : ℕ} {Z : Matrix (Fin n) (Fin n) K}
    {Z' : Matrix (Fin n') (Fin n') K} {Z'' : Matrix (Fin n'') (Fin n'') K}
    {φ : coker R Z ≃ₗ[R] coker R Z'} {φ' : coker R Z' ≃ₗ[R] coker R Z''}
    (h : φ ∈ isoZZ R Z Z') (h' : φ' ∈ isoZZ R Z' Z'') : φ.trans φ' ∈ isoZZ R Z Z'' := by
  refine ⟨by simp [h.1, h'.1], fun v v'' hv => ?_⟩
  obtain ⟨v', hv'⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
  simp only [LinearEquiv.trans_apply] at hv
  rw [← hv'] at hv
  rw [h'.2 v' v'' hv, h.2 v v' hv'.symm]
end Formalism.FourierDecayAlt.P.A5x4
