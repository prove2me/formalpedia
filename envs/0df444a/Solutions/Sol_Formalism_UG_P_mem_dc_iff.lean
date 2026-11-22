-- Prove2me | solution 1 for Formalism.UG.P.mem_dc_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:56:14.127628+00:00
-- url     : https://prove2.me/submissions/da848f01-bf88-4944-88f6-8d10e09904d5

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
theorem _root_.solution (K : Subgroup G) (g x : G) :
    x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔
      ∃ a : K, ∃ b : K, x = (a : G) * g * b := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, a.2, b, b.2, rfl⟩
end Formalism.UG.P
