-- Prove2me | solution 1 for Formalism.UG.P.dosetInd_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:12.067833+00:00
-- url     : https://prove2.me/submissions/ea7a6915-3d2b-44a8-a157-ad7b7d68edff

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
theorem _root_.solution (k : Type) [CommRing k] (K : Subgroup G) (g x : G)
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) : dosetInd k K g x = 1 := by
  simp [dosetInd, hx]
end Formalism.UG.P
