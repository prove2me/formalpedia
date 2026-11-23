-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.vlet_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:01.496292+00:00
-- url     : https://prove2.me/submissions/aeebec09-2600-483c-a02f-1ff09c2770a3

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_free

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
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (σ : Site A) (l : Letter K S) {a : S} (h : a ≠ l.intersection_update_fsHerm_neg_one) : FreeOf a (vlet σ l) :=
  ins_free h _ fun _ _ => io_free a _
end Formalism.FourierDecayAlt.P.Wd6
