-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.feasible_run
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:30.173207+00:00
-- url     : https://prove2.me/submissions/e565006c-f183-41d6-b416-1bf302e514d8

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointAlgorithm
import Theorems.Thm_ConsistentSubmodular_Checkpoints_card_path_le
import Theorems.Thm_ConsistentSubmodular_Checkpoints_recourse_path_le
import Theorems.Thm_ConsistentSubmodular_Checkpoints_recourse_arrival_le
import Theorems.Thm_ConsistentSubmodular_Checkpoints_run_eq

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

theorem pre_subset (D : Finset (Fin n)) (r : ℕ) : pre D r ⊆ D := by
  intro x hx
  exact Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))

theorem path_subset (C A : Finset (Fin n)) (r : ℕ) : path C A r ⊆ C ∪ A := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp (pre_subset _ _ hx)).1

/-- The recourse between two unions is at most the sum of the recourses. -/
theorem recourse_union_le (X Y X' Y' : Finset (Fin n)) :
    recourse (X ∪ Y) (X' ∪ Y') ≤ recourse X X' + recourse Y Y' := by
  unfold recourse
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
  tauto

theorem elapsed_succ_le (ℓ h σ r : ℕ) : elapsed ℓ h σ (r + 1) ≤ elapsed ℓ h σ r + 1 := by
  unfold elapsed
  omega

theorem elapsed_mono (ℓ h σ : ℕ) {r r' : ℕ} (hr : r ≤ r') :
    elapsed ℓ h σ r ≤ elapsed ℓ h σ r' := by
  unfold elapsed
  omega

theorem done_mono (ℓ h s R σ : ℕ) {r r' : ℕ} (hr : r ≤ r') :
    done ℓ h s R σ r ≤ done ℓ h s R σ r' :=
  min_le_min_left R (Nat.mul_le_mul_left s (elapsed_mono ℓ h σ hr))

theorem done_succ_le (ℓ h s R σ r : ℕ) :
    done ℓ h s R σ (r + 1) ≤ done ℓ h s R σ r + s := by
  have he := elapsed_succ_le ℓ h σ r
  have hm : s * elapsed ℓ h σ (r + 1) ≤ s * elapsed ℓ h σ r + s := by
    calc s * elapsed ℓ h σ (r + 1) ≤ s * (elapsed ℓ h σ r + 1) := Nat.mul_le_mul_left s he
      _ = s * elapsed ℓ h σ r + s := by ring
  unfold done
  omega

end ConsistentSubmodular.Checkpoints

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

theorem arrivedPrefix_mono {a b : ℕ} (h : a ≤ b) : arrivedPrefix n a ⊆ arrivedPrefix n b := by
  intro e he
  simp only [arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  omega

theorem future_subset (c j : ℕ) : future n c j ⊆ arrivedPrefix n (c + j) := by
  intro e he
  simp only [future, arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  omega

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

theorem oldCore_subset (hg : Good P A σ) (i : ℕ) : oldCore n P.ℓ A i ⊆ arrivedPrefix n (i * P.ℓ) := by
  unfold oldCore
  split_ifs with hi
  · exact Finset.empty_subset _
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j + 1 - 1 = j := by omega
    rw [hj, Finset.union_subset_iff]
    have he : (j + 1) * P.ℓ = j * P.ℓ + P.ℓ := by ring
    rw [he]
    exact ⟨(hg j).2.1.trans (arrivedPrefix_mono (by omega)), future_subset _ _⟩

theorem card_oldCore_le (hg : Good P A σ) (i : ℕ) : (oldCore n P.ℓ A i).card ≤ P.κ + P.ℓ := by
  unfold oldCore
  split_ifs with hi
  · simp
  · exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (hg (i - 1)).2.2 (card_future_le _ _))

theorem state_zero (i : ℕ) : state P A σ i 0 = oldCore n P.ℓ A i := by
  have hd : done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) 0 = 0 := by
    simp [done, elapsed]
  have hb : block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + 0) = ∅ := by
    rw [block_inter _ _ _ (Nat.zero_le _)]
    ext e
    simp [future]
  rw [state, hd, path_zero, hb, Finset.union_empty]

theorem state_subset (hg : Good P A σ) (i r : ℕ) :
    state P A σ i r ⊆ arrivedPrefix n (i * P.ℓ + r) := by
  rw [state, Finset.union_subset_iff]
  refine ⟨(path_subset _ _ _).trans ?_, Finset.inter_subset_right⟩
  rw [Finset.union_subset_iff]
  exact ⟨(oldCore_subset hg i).trans (arrivedPrefix_mono (by omega)),
    (hg i).2.1.trans (arrivedPrefix_mono (by omega))⟩

theorem card_state_le (hP : P.Valid k) (hg : Good P A σ) (i r : ℕ) :
    (state P A σ i r).card ≤ k := by
  have h1 := Finset.card_union_le
    (path (oldCore n P.ℓ A i) (A i)
      (done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r))
    (block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + r))
  have h2 := card_path_le (oldCore n P.ℓ A i) (A i)
    (done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r)
  have h3 : (block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + r)).card ≤ P.ℓ :=
    (Finset.card_le_card Finset.inter_subset_left).trans (card_future_le _ _)
  have h4 := card_oldCore_le hg i
  have h5 := (hg i).2.2
  have h6 := hP.budget
  rw [state]
  omega

/-- Each update changes at most `2s + 1` elements: at most `s` operations, each
changing two elements, and the new arrival. -/
theorem recourse_state_succ (i r : ℕ) :
    recourse (state P A σ i (r + 1)) (state P A σ i r) ≤ 2 * P.s + 1 := by
  refine (recourse_union_le _ _ _ _).trans ?_
  have hmono := done_mono P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i)
    (Nat.le_add_right r 1)
  have hpath := recourse_path_le (oldCore n P.ℓ A i) (A i) hmono
  have hsucc := done_succ_le P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r
  have harr := recourse_arrival_le (block n P.ℓ i) (i * P.ℓ + r)
  rw [show i * P.ℓ + (r + 1) = i * P.ℓ + r + 1 by ring]
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

theorem solution (hP : P.Valid k) (hg : Good P A σ) :
    FeasibleTrajectory k (2 * P.s + 1) (fun t : Fin (n + 1) => run P A σ t.val) := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩, fun u => ?_⟩
  · show run P A σ 0 = ∅
    have h := run_eq hP hg 0
    rw [Nat.zero_div, Nat.zero_mod, state_zero] at h
    rw [h]
    simp [oldCore]
  · show run P A σ t.val ⊆ arrivedPrefix n t.val
    rw [run_eq hP hg]
    have := state_subset hg (t.val / P.ℓ) (t.val % P.ℓ)
    rwa [Nat.div_add_mod'] at this
  · show (run P A σ t.val).card ≤ k
    rw [run_eq hP hg]
    exact card_state_le hP hg _ _
  · show recourse (run P A σ (u.val + 1)) (run P A σ u.val) ≤ 2 * P.s + 1
    rw [run_succ, run_eq hP hg]
    exact recourse_state_succ _ _

end
