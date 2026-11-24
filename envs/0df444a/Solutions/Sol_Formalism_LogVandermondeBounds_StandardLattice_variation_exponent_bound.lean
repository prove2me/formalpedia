-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.variation_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:59.515519+00:00
-- url     : https://prove2.me/submissions/d1543cf2-3cb5-496b-8e54-c21a4d4cc820

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_ind_sum_le
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_pair_bound
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_harm_double

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
theorem _root_.solution : LogVandermondeVariation := by
  intro n Δ u u' hw
  have hΔ := hw.1
  have hL : 0 ≤ Real.log (1 + Δ) := Real.log_nonneg (by linarith)
  have e : vandLog u - vandLog u' = ∑ a, ∑ b ∈ univ.filter (fun b => a < b),
      (Real.log (u a - u b) - Real.log (u' a - u' b)) := by
    unfold vandLog
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_sub_distrib]
  rw [e]
  have hsum := harm_double (n + 2)
  have i0 := ind_sum_le (0 : Fin (n + 2)) ⟨1, by omega⟩ (Real.log (1 + Δ)) hL
  have i1 := ind_sum_le (⟨n, by omega⟩ : Fin (n + 2)) (Fin.last (n + 1)) (Real.log (1 + Δ)) hL
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  push_cast at hsum
  calc |∑ a, ∑ b ∈ univ.filter (fun b => a < b), (Real.log (u a - u b) - Real.log (u' a - u' b))|
      ≤ ∑ a, ∑ b ∈ univ.filter (fun b => a < b), |Real.log (u a - u b) - Real.log (u' a - u' b)| :=
        (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) +
      ((if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0) +
       (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0))) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b hb
        exact pair_bound hw a b (by simpa using hb)
    _ = (∑ a : Fin (n + 2), ∑ b ∈ univ.filter (fun b => a < b), 2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1)) +
        ((∑ a : Fin (n + 2), ∑ b ∈ univ.filter (fun b => a < b),
          (if a = 0 ∧ b = ⟨1, by omega⟩ then Real.log (1 + Δ) else 0)) +
        (∑ a : Fin (n + 2), ∑ b ∈ univ.filter (fun b => a < b),
          (if a = ⟨n, by omega⟩ ∧ b = Fin.last (n + 1) then Real.log (1 + Δ) else 0))) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ 6 * (n + 2) * (1 + Real.log (n + 2)) + 2 * Real.log (1 + Δ) := by
        have : 0 ≤ ((n : ℝ) + 2) * (1 + Real.log ((n : ℝ) + 2)) := by positivity
        nlinarith
end Formalism.LogVandermondeBounds.StandardLattice
