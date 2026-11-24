-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.scalar_commute_transposed_R_matrix_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:38.837107+00:00
-- url     : https://prove2.me/submissions/5ada2ca9-316c-444f-bf17-d267274cefbe

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_comm_eU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (a : S) (D : K) (z : A) (i j : Fin 2) :
    Commute (io z : SlopeTestRemainingChoices S A) (Rht0 a D i j) := by
  have h : (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) i j =
      (D - 1)⁻¹ • (D • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU a i j) := rfl
  rw [h]
  refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _) (io_comm_eU a i j z).symm) _
  rw [Matrix.one_apply]
  split_ifs
  · exact Commute.one_right _
  · exact Commute.zero_right _
end Formalism.FourierDecayAlt.P.Wd7
