-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.lamTil_eLast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:20.814217+00:00
-- url     : https://prove2.me/submissions/b2a48c11-91fd-4a36-9c16-105228dab6a0

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_fin
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) K) (a b : Fin n) (hb : b.val + 1 = n) :
    lamTil R Z a.val (eLast R) = Z⁻¹ a b := by
  rw [lamTil_fin]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single b]
  · simp [coeLin_apply, eLast, hb]
  · intro c _ hc
    have : ¬ (c.val + 1 = n) := fun h => hc (Fin.ext (by omega))
    simp [coeLin_apply, eLast, this]
  · simp
end Formalism.FourierDecayAlt.P.A5x2
