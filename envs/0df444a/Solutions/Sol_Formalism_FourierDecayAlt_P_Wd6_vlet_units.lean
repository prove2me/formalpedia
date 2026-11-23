-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.vlet_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:40.344799+00:00
-- url     : https://prove2.me/submissions/cf2affce-6790-4a69-adcc-bb3f753f2db4

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_vlet_free

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
theorem _root_.solution (σ : Site A) (l : Letter K S) (w : List (Letter K S))
    (h : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one) : ∀ l' ∈ w, ∀ i j, Commute (vlet σ l) (eU l'.intersection_update_fsHerm_neg_one i j) := by
  intro l' hl' i j
  have hne : l'.intersection_update_fsHerm_neg_one ≠ l.intersection_update_fsHerm_neg_one := by
    intro e
    exact h (e ▸ List.mem_map_of_mem hl')
  exact (vlet_free σ l hne i j).symm
end Formalism.FourierDecayAlt.P.Wd6
