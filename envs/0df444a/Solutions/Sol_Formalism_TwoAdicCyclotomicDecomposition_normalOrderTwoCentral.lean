-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.normalOrderTwoCentral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:36.856069+00:00
-- url     : https://prove2.me/submissions/36c0fed6-527f-4fdd-9eb2-085cc6577b32

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : NormalOrderTwoCentral := by
  intro H _ N hN h2 z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · simp [hz1]
  have hc : g * z * g⁻¹ ∈ N := hN.conj_mem z hz g
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp h2
  have e1 : (⟨g * z * g⁻¹, hc⟩ : N) = y := huniq _ (by
    intro h; apply hz1
    have h' : g * z * g⁻¹ = 1 := congrArg Subtype.val h
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group)
  have e2 : (⟨z, hz⟩ : N) = y := huniq _ (by
    intro h; exact hz1 (congrArg Subtype.val h))
  have : g * z * g⁻¹ = z := congrArg Subtype.val (e1.trans e2.symm)
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [this]
end Formalism.TwoAdicCyclotomicDecomposition
