-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.run_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:48.220989+00:00
-- url     : https://prove2.me/submissions/423b4f80-e52b-4145-8385-05ccf68d2f9e

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

theorem hi_le (ℓ h : ℕ) {σ : ℕ} (hσ : σ < h) : hi ℓ h σ ≤ ℓ := by
  rcases Nat.eq_zero_or_pos h with hh | hh
  · omega
  calc (σ + 1) * ℓ / h ≤ h * ℓ / h := Nat.div_le_div_right (Nat.mul_le_mul_right ℓ hσ)
    _ = ℓ := Nat.mul_div_cancel_left ℓ hh

theorem elapsed_of_hi_le {ℓ h σ r : ℕ} (hr : hi ℓ h σ ≤ r) :
    elapsed ℓ h σ r = hi ℓ h σ - lo ℓ h σ := by
  unfold elapsed
  rw [min_eq_left hr]

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

theorem state_zero (i : ℕ) : state P A σ i 0 = oldCore n P.ℓ A i := by
  have hd : done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) 0 = 0 := by
    simp [done, elapsed]
  have hb : block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + 0) = ∅ := by
    rw [block_inter _ _ _ (Nat.zero_le _)]
    ext e
    simp [future]
  rw [state, hd, path_zero, hb, Finset.union_empty]

/-- At the end of block `i` the algorithm holds `A_i ∪ B_{i+1}`, the old core of
the next block. -/
theorem state_last (hP : P.Valid k) (hg : Good P A σ) (i : ℕ) :
    state P A σ i P.ℓ = oldCore n P.ℓ A (i + 1) := by
  have hd := done_complete hP hg i (hi_le P.ℓ P.h (hg i).1)
  rw [state, hd, path_of_operations_le _ _ le_rfl, block_inter _ _ _ le_rfl]
  simp [oldCore, block]

end ConsistentSubmodular.Checkpoints

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}
variable {P : Params} {A : ℕ → Finset (Fin n)} {σ : ℕ → ℕ} {k : ℕ}

theorem solution (hP : P.Valid k) (hg : Good P A σ) (u : ℕ) :
    run P A σ u = state P A σ (u / P.ℓ) (u % P.ℓ) := by
  have hℓ := hP.block_pos
  have hd := Nat.div_add_mod' u P.ℓ
  have hm := Nat.mod_lt u hℓ
  simp only [run, pos, phase]
  rcases Nat.eq_zero_or_pos u with hu | hu
  · subst hu
    simp
  rcases Nat.eq_zero_or_pos (u % P.ℓ) with hq | hq
  · -- `u = i ℓ` with `i ≥ 1`: the end of block `i - 1`.
    obtain ⟨j, hj⟩ : ∃ j, u / P.ℓ = j + 1 := ⟨u / P.ℓ - 1, by
      rcases Nat.eq_zero_or_pos (u / P.ℓ) with h0 | h0
      · rw [h0, hq] at hd
        omega
      · omega⟩
    have hu' : u = j * P.ℓ + P.ℓ := by
      rw [hj, hq] at hd
      linarith
    have hdiv : (u - 1) / P.ℓ = j := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [add_one_mul]
        omega
    rw [hdiv, hj, hq, state_zero, ← state_last hP hg j]
    congr 1
    omega
  · have hdiv : (u - 1) / P.ℓ = u / P.ℓ := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [add_one_mul]
        omega
    rw [hdiv]
    congr 1
    omega

end
