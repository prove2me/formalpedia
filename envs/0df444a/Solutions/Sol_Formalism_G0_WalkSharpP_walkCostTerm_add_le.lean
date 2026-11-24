-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.walkCostTerm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:25.226288+00:00
-- url     : https://prove2.me/submissions/d31221bd-9f2a-4030-babd-56b261ea6446

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Theorems.Thm_Formalism_G0_WalkSharpP_accT_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
namespace Formalism.G0.WalkSharpP
theorem _root_.solution {V : ℕ} (a b c : Fin V → ℕ) (m c₀ : ℕ) {B : Finset (Fin V)}
    {i : Fin V → ℕ} (hi : ∀ u ∈ B, i u < m) {t : Fin V} (ht : t ∈ B) (u : Fin V) :
    accT a b c m c₀ B i u + (if u = t then c₀ else 0) ≤ a u + b u + (m - 1) * c u + m * c₀ := by

  by_cases hut : u = t
  · subst t
    have h : accT a b c m c₀ B i u = b u + i u * (c u + c₀) := by simp [accT, ht]
    have := hi u ht
    have e1 : i u * c u ≤ (m - 1) * c u := Nat.mul_le_mul_right _ (by omega)
    have e2 : (i u + 1) * c₀ ≤ m * c₀ := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, one_mul] at e2
    rw [h, if_pos rfl, Nat.mul_add]
    omega
  · rw [if_neg hut, add_zero]
    exact accT_le a b c m c₀ hi u
end Formalism.G0.WalkSharpP
