-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.Xm_EC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:34.511243+00:00
-- url     : https://prove2.me/submissions/4f6ac9ef-5890-4125-9e9a-3ed24716da9e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_EC_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_EC_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_entry_commute_transposed_R_matrix

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
    (h : ∀ l ∈ w, ∀ i j, Commute z (eU l.intersection_update_fsHerm_neg_one i j)) : EC z (Xm w Y) := by
  induction w with
  | nil => exact EC.one z
  | cons l w ih =>
    have ih' := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    unfold Xm
    split_ifs
    · exact ih'
    · exact (entry_commute_transposed_R_matrix (h l List.mem_cons_self) _).mul ih'
end Formalism.FourierDecayAlt.P.Wd6
