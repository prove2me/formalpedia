-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.lower_right_block_is_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:16.409886+00:00
-- url     : https://prove2.me/submissions/a52dfa1e-4e2d-4241-a85d-31dbb0e2d542

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {p : Matrix (Fin n) (Fin n) K} (hp : IsP R k p) : IsD R k (b22 k p) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    simp only [b22]
    split_ifs
    · exact up_zero hp.1 hab'
    · exact Matrix.one_apply_ne (ne_of_gt hab')
  · intro a
    simp only [b22]
    split_ifs
    · exact hp.1.2 a
    · exact Matrix.one_apply_eq a
  · intro a b
    simp only [b22]
    split_ifs with h
    · exact hp.2 a b (Or.inl h)
    · rw [Matrix.one_apply]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem
  · intro a b ha
    simp only [b22]
    rw [if_neg (by omega)]
end Formalism.FourierDecayAlt.P.A5x9
