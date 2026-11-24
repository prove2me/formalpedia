-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.gap_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:47.116036+00:00
-- url     : https://prove2.me/submissions/5f5d9ee8-ce53-4611-8cd1-19949d07fd44

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution {n : ℕ} (u : Fin (n + 2) → ℝ) (g : ℝ)
    (h : ∀ i j : Fin (n + 2), 1 ≤ i.val → j.val = i.val + 1 → j.val ≤ n → g ≤ u i - u j)
    (a : Fin (n + 2)) (ha : 1 ≤ a.val) :
    ∀ m : ℕ, ∀ b : Fin (n + 2), b.val = a.val + m → b.val ≤ n → g * m ≤ u a - u b := by
  intro m
  induction m with
  | zero =>
    intro b hb _
    have : b = a := Fin.ext (by omega)
    subst this; simp
  | succ m ih =>
    intro b hb hbn
    let c : Fin (n + 2) := ⟨a.val + m, by omega⟩
    have h1 := ih c rfl (by simp [c]; omega)
    have h2 := h c b (by simp [c]; omega) (by simp [c]; omega) hbn
    push_cast
    linarith
end Formalism.LogVandermondeBounds.StandardLattice
