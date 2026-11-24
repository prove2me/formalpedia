-- Prove2me | solution 1 for Formalism.UG.P.dc_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:07.131941+00:00
-- url     : https://prove2.me/submissions/1ce755ca-3e1e-4ac6-958c-48e4f9b38026

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
theorem _root_.solution (K : Subgroup G) (g : G) (a b : K) (x : G)
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) :
    (a : G) * x * b ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
  rw [mem_dc_iff] at hx ⊢
  obtain ⟨c, d, rfl⟩ := hx
  exact ⟨a * c, d * b, by simp [mul_assoc]⟩
end Formalism.UG.P
