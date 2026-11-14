-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.value_le_run
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:48.782149+00:00
-- url     : https://prove2.me/submissions/f0d2f21c-e087-4269-bde4-90f102583837

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointAlgorithm

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

theorem pre_of_card_le (D : Finset (Fin n)) {r : ℕ} (h : D.card ≤ r) : pre D r = D := by
  rw [pre, List.take_of_length_le (by rw [Finset.length_toList]; exact h),
    Finset.toList_toFinset]

theorem path_of_operations_le (C A : Finset (Fin n)) {r : ℕ} (h : operations C A ≤ r) :
    path C A r = A := by
  have h1 : (C \ A).card ≤ r := le_trans (le_max_left _ _) h
  have h2 : (A \ C).card ≤ r := le_trans (le_max_right _ _) h
  rw [path, pre_of_card_le _ h1, pre_of_card_le _ h2]
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- Each subblock has at least `⌊ℓ/h⌋` updates. -/
theorem div_le_hi_sub_lo (ℓ h σ : ℕ) : ℓ / h ≤ hi ℓ h σ - lo ℓ h σ := by
  have h1 := Nat.add_div_le_add_div (σ * ℓ) ℓ h
  have h2 : (σ + 1) * ℓ = σ * ℓ + ℓ := by ring
  unfold hi lo
  rw [h2]
  omega

theorem elapsed_of_le_lo {ℓ h σ r : ℕ} (hr : r ≤ lo ℓ h σ) : elapsed ℓ h σ r = 0 := by
  unfold elapsed
  omega

theorem elapsed_of_hi_le {ℓ h σ r : ℕ} (hr : hi ℓ h σ ≤ r) :
    elapsed ℓ h σ r = hi ℓ h σ - lo ℓ h σ := by
  unfold elapsed
  rw [min_eq_left hr]

theorem done_of_le_lo {ℓ h s R σ r : ℕ} (hr : r ≤ lo ℓ h σ) : done ℓ h s R σ r = 0 := by
  simp [done, elapsed_of_le_lo hr]

theorem done_of_hi_le {ℓ h s R σ r : ℕ} (hr : hi ℓ h σ ≤ r)
    (hR : R ≤ s * (hi ℓ h σ - lo ℓ h σ)) : done ℓ h s R σ r = R := by
  rw [done, elapsed_of_hi_le hr]
  exact min_eq_left hR

end ConsistentSubmodular.Checkpoints

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

theorem card_future_le (c j : ℕ) : (future n c j).card ≤ j := by
  have hsub : (future n c j).map Fin.valEmbedding ⊆ Finset.Ico c (c + j) := by
    intro x hx
    simp only [Finset.mem_map, future, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact Finset.mem_Ico.mpr he
  have h := Finset.card_le_card hsub
  simpa using h

theorem block_inter (ℓ i r : ℕ) (hr : r ≤ ℓ) :
    block n ℓ i ∩ arrivedPrefix n (i * ℓ + r) = future n (i * ℓ) r := by
  ext e
  simp only [block, future, arrivedPrefix, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and]
  omega

variable {P : Params} {A : ℕ → Finset (Fin n)} {σ : ℕ → ℕ} {k : ℕ}

theorem card_oldCore_le (hg : Good P A σ) (i : ℕ) : (oldCore n P.ℓ A i).card ≤ P.κ + P.ℓ := by
  unfold oldCore
  split_ifs with hi
  · simp
  · exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (hg (i - 1)).2.2 (card_future_le _ _))

theorem operations_le_max (C A : Finset (Fin n)) : operations C A ≤ max C.card A.card :=
  max_le_max (Finset.card_le_card Finset.sdiff_subset) (Finset.card_le_card Finset.sdiff_subset)

theorem operations_le (hP : P.Valid k) (hg : Good P A σ) (i : ℕ) :
    operations (oldCore n P.ℓ A i) (A i) ≤ k := by
  have h1 := operations_le_max (oldCore n P.ℓ A i) (A i)
  have h2 := card_oldCore_le hg i
  have h3 := (hg i).2.2
  have h4 := hP.budget
  omega

/-- The transition of block `i` is finished at the end of the selected subblock. -/
theorem done_complete (hP : P.Valid k) (hg : Good P A σ) (i : ℕ) {r : ℕ}
    (hr : hi P.ℓ P.h (σ i) ≤ r) :
    done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r =
      operations (oldCore n P.ℓ A i) (A i) := by
  apply done_of_hi_le hr
  have h1 := operations_le hP hg i
  have h2 := hP.complete
  have h3 := Nat.mul_le_mul_left P.s (div_le_hi_sub_lo P.ℓ P.h (σ i))
  omega

/-- Time `u + 1` is update `u % ℓ + 1` of block `u / ℓ`. -/
theorem run_succ (u : ℕ) :
    run P A σ (u + 1) = state P A σ (u / P.ℓ) (u % P.ℓ + 1) := by
  have hd := Nat.div_add_mod' u P.ℓ
  simp only [run, pos, phase, Nat.add_sub_cancel]
  congr 1
  omega

end ConsistentSubmodular.Checkpoints

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}
variable {P : Params} {A : ℕ → Finset (Fin n)} {σ : ℕ → ℕ} {k : ℕ}

theorem solution (hP : P.Valid k) (hg : Good P A σ) (f : Objective n) (u : ℕ) :
    (if u % P.ℓ + 1 ≤ lo P.ℓ P.h (σ (u / P.ℓ)) then
        f.value (oldCore n P.ℓ A (u / P.ℓ) ∪ future n (u / P.ℓ * P.ℓ) (u % P.ℓ + 1)) else 0) +
      (if ¬ u % P.ℓ + 1 ≤ lo P.ℓ P.h (σ (u / P.ℓ)) ∧
          hi P.ℓ P.h (σ (u / P.ℓ)) ≤ u % P.ℓ + 1 then
        f.value (A (u / P.ℓ) ∪ future n (u / P.ℓ * P.ℓ) (u % P.ℓ + 1)) else 0) ≤
      f.value (run P A σ (u + 1)) := by
  have hℓ := hP.block_pos
  have hr : u % P.ℓ + 1 ≤ P.ℓ := Nat.mod_lt u hℓ
  rw [run_succ, state, block_inter _ _ _ hr]
  set i := u / P.ℓ
  set r := u % P.ℓ + 1
  by_cases h1 : r ≤ lo P.ℓ P.h (σ i)
  · rw [if_pos h1, if_neg (fun h => h.1 h1), add_zero, done_of_le_lo h1, path_zero]
  · rw [if_neg h1, zero_add]
    split_ifs with h2
    · rw [done_complete hP hg i h2.2, path_of_operations_le _ _ le_rfl]
    · exact f.nonnegative _

end
