-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.rtt_relation_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:29.114023+00:00
-- url     : https://prove2.me/submissions/c89a7bfb-4a93-4dd7-809c-7d084281d4fd

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_entry_commute_R_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_Rh0_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_rtt_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transp_exch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (b : S) (M V : M2 A) (d : K) (h : Rel M V d) :
    lift0 Mᵀ * Rht0 b d * d0 (ins b (lift0 V)) = d0 (ins b (lift0 V)) * Rht0 b d * lift0 Mᵀ := by
  have hc : ∀ i j, EC ((Rh0 b d : M2 (SlopeTestRemainingChoices S A)) i j) (lift0 M) := fun i j k l =>
    (entry_commute_R_matrix (z := io (M k l)) (fun r s => (eU_io b r s _).symm) d i j).symm
  have := transp_exch hc (rtt_relation b M V d h)
  rw [Rh0_transpose] at this
  exact this
end Formalism.FourierDecayAlt.P.Wd6
