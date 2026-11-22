-- Prove2me | solution 1 for Formalism.L2.G.Cmp.Fib.mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:06.25809+00:00
-- url     : https://prove2.me/submissions/37471af9-5679-40ad-8cca-04fa7b866498

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsFib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.UG
open Formalism.L2.G.Cmp.Fib
variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)
namespace Formalism.L2.G.Cmp.Fib
theorem _root_.solution (S : Subgroup G) (a b : G) :
    (mkC H S a = mkC H S b) ↔ ∃ h ∈ H, ∃ κ ∈ S, b = h * a * κ := by
  unfold mkC
  exact DoubleCoset.eq _ _ a b
end Formalism.L2.G.Cmp.Fib
