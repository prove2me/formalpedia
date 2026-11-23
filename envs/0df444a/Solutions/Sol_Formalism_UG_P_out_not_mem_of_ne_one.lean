-- Prove2me | solution 1 for Formalism.UG.P.out_not_mem_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:05.771405+00:00
-- url     : https://prove2.me/submissions/c7424142-c5c3-4746-b95d-69e355988d10

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution (K : Subgroup G) (x : G ⧸ K) (hx : x ≠ ((1 : G) : G ⧸ K)) :
    x.out ∉ K := by
  intro h
  apply hx
  rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
  simpa using h
end Formalism.UG.P
