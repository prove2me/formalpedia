-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.Lst_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:25.433109+00:00
-- url     : https://prove2.me/submissions/7f08e16f-b4b8-4da8-ac6a-327e42750474

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Lst_nodup

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
theorem _root_.solution {n i : ℕ} (hi : i < n) : (Lst n i).toFinset = (Finset.range n).erase i := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_erase, Finset.mem_range] at hx
    rw [List.mem_toFinset]
    unfold Lst
    rw [List.mem_map]

    refine ⟨(x + n - i) % n - 1, ?_, ?_⟩
    · rw [List.mem_range]
      have := Nat.mod_lt (x + n - i) (by omega : 0 < n)
      omega
    · have hne : (x + n - i) % n ≠ 0 := by
        intro h0
        have h1 : (x + n - i) % n = (i + n - i) % n := by rw [h0]; simp
        by_cases hxi : i ≤ x
        · have : x - i < n := by omega
          have e1 : (x + n - i) % n = (x - i) % n := by
            rw [show x + n - i = (x - i) + n by omega, Nat.add_mod_right]
          rw [e1, Nat.mod_eq_of_lt this] at h0
          omega
        · have : x + n - i < n := by omega
          rw [Nat.mod_eq_of_lt this] at h0
          omega
      rw [add_assoc, Nat.sub_add_cancel (Nat.pos_of_ne_zero hne)]
      rw [Nat.add_mod_mod]
      rw [show i + (x + n - i) = x + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx.2]
  · rw [List.toFinset_card_of_nodup (Lst_nodup n i), Finset.card_erase_of_mem (Finset.mem_range.2 hi)]
    simp [Lst]
end Formalism.G0.TopsWeightFunctionBounds
