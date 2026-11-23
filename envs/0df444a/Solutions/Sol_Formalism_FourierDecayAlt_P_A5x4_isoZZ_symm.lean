-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.isoZZ_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:18.614089+00:00
-- url     : https://prove2.me/submissions/ea455b68-c06c-4521-81e2-c2563c69e41a

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
theorem _root_.solution {n n' : ℕ} {Z : Matrix (Fin n) (Fin n) K} {Z' : Matrix (Fin n') (Fin n') K}
    {φ : coker R Z ≃ₗ[R] coker R Z'} (h : φ ∈ isoZZ R Z Z') : φ.symm ∈ isoZZ R Z' Z := by
  refine ⟨by rw [← h.1]; simp, fun v' v hv => ?_⟩
  have : φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by rw [← hv]; simp
  exact (h.2 v v' this).symm
end Formalism.FourierDecayAlt.P.A5x4
