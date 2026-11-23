-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.Xp_EC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:59.949836+00:00
-- url     : https://prove2.me/submissions/c31696d1-6cf9-4808-9947-d46d7d4d7bd9

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_EC_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_EC_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_entry_commute_R_matrix

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
theorem _root_.solution {z : SlopeTestRemainingChoices S A} (w : List (Letter K S)) (Y : K)
    (h : ∀ l ∈ w, ∀ i j, Commute z (eU l.intersection_update_fsHerm_neg_one i j)) : EC z (Xp w Y) := by
  induction w with
  | nil => exact EC.one z
  | cons l w ih =>
    have ih' := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    unfold Xp
    split_ifs
    · exact ih'.mul (entry_commute_R_matrix (h l List.mem_cons_self) _)
    · exact ih'
end Formalism.FourierDecayAlt.P.Wd6
