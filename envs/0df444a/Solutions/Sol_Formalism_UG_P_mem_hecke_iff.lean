-- Prove2me | solution 1 for Formalism.UG.P.mem_hecke_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:56:18.370428+00:00
-- url     : https://prove2.me/submissions/fbd4bfe3-00f7-4b89-9727-8a818ca850ff

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
theorem _root_.solution (k : Type) [CommRing k] (K : Subgroup G) (f : G → k) :
    f ∈ Hecke k K ↔ IsBiInv K f ∧ FinDosetSupp K f := Iff.rfl
end Formalism.UG.P
