-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.sum_list
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:25.258805+00:00
-- url     : https://prove2.me/submissions/c3beb83c-2f74-4393-817a-98e17dbd7daa

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_runS_cons

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
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (l : List ℕ) (hl : l.Nodup) : ∀ s : St,
    ∑ U ∈ l.toFinset.powerset,
      (if runS R L₂ s (l.map (fun p => decide (p ∈ U))) = .bad then
        ∏ p ∈ l.toFinset, wP δ U p else 0) = Wt R L₂ δ l.length s := by
  induction l with
  | nil => intro s; simp [Wt, runS]
  | cons p l ih =>
    intro s
    rw [List.nodup_cons] at hl
    obtain ⟨hp, hl'⟩ := hl
    have hp' : p ∉ l.toFinset := by simpa using hp
    rw [List.toFinset_cons, Finset.sum_powerset_insert hp']
    have e1 : ∀ U ∈ l.toFinset.powerset,
        (if runS R L₂ s ((p :: l).map (fun q => decide (q ∈ U))) = .bad then
          ∏ q ∈ insert p l.toFinset, wP δ U q else 0) =
        (1 - δ) * (if runS R L₂ (step R L₂ s false) (l.map (fun q => decide (q ∈ U))) = .bad then
          ∏ q ∈ l.toFinset, wP δ U q else 0) := by
      intro U hU
      have hpU : p ∉ U := fun h => hp' (Finset.mem_powerset.1 hU h)
      have hw : wP δ U p = 1 - δ := by simp [wP, hpU]
      rw [Finset.prod_insert hp', hw, List.map_cons, runS_cons, decide_eq_false hpU]
      split_ifs <;> ring
    have e2 : ∀ U ∈ l.toFinset.powerset,
        (if runS R L₂ s ((p :: l).map (fun q => decide (q ∈ insert p U))) = .bad then
          ∏ q ∈ insert p l.toFinset, wP δ (insert p U) q else 0) =
        δ * (if runS R L₂ (step R L₂ s true) (l.map (fun q => decide (q ∈ U))) = .bad then
          ∏ q ∈ l.toFinset, wP δ U q else 0) := by
      intro U _
      have hmap : l.map (fun q => decide (q ∈ insert p U)) = l.map (fun q => decide (q ∈ U)) := by
        apply List.map_congr_left
        intro q hq
        have : q ≠ p := fun h => hp (h ▸ hq)
        simp [Finset.mem_insert, this]
      have hprod : ∏ q ∈ l.toFinset, wP δ (insert p U) q = ∏ q ∈ l.toFinset, wP δ U q := by
        apply Finset.prod_congr rfl
        intro q hq
        have : q ≠ p := fun h => hp' (h ▸ hq)
        simp [wP, Finset.mem_insert, this]
      have hw : wP δ (insert p U) p = δ := by simp [wP]
      rw [Finset.prod_insert hp', hw, List.map_cons, runS_cons, hmap, hprod,
        decide_eq_true (Finset.mem_insert_self p U)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum,
      ih hl', ih hl']
    simp only [List.length_cons, Wt]
    ring
end Formalism.G0.TopsWeightFunctionBounds
