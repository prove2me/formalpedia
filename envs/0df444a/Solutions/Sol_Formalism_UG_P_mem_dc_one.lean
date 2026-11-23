-- Prove2me | solution 1 for Formalism.UG.P.mem_dc_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:02.795856+00:00
-- url     : https://prove2.me/submissions/246aab64-b30f-447b-9cb3-bc806f6c2717

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Theorems.Thm_Formalism_UG_P_mem_dc_iff

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
theorem _root_.solution (K : Subgroup G) (x : G) :
    x ∈ DoubleCoset.doubleCoset (1 : G) (K : Set G) (K : Set G) ↔ x ∈ K := by
  rw [mem_dc_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    rw [mul_one]
    exact K.mul_mem a.2 b.2
  · intro hx
    exact ⟨⟨x, hx⟩, 1, by simp⟩
end Formalism.UG.P
