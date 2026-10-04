-- Prove2me | solution 1 for Disjunctive.HigherDim.sherali_adams_subset_iterated_split
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:31:59.439899+00:00
-- url     : https://prove2.me/submissions/e9ce7892-afbc-4274-9858-10230179a6a6

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts

/-! Counterexample: with `m = 0` (no rows), the Sherali-Adams lift `KtSet` imposes no inequality,
so it is all of `ℝ¹`, while the split hull over `S = {0}` lies in `{x | x 0 ≤ 1}`. -/

open Disjunctive.HigherDim in
theorem kt_mem_57229d57 :
    (fun _ => (2 : ℝ)) ∈ KtSet (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 Finset.univ 1 := by
  refine ⟨fun J => if J = ∅ then 1 else 2, fun _ _ => 2, ?_, ?_, ?_, ?_⟩
  · simp
  · intro j _
    simp
  · intro k hk
    exact absurd (Finset.mem_univ k) hk
  · intro i
    exact Fin.elim0 i

open Disjunctive.HigherDim in
theorem hull_le_57229d57 :
    convexHull ℝ (Poly (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 ∩ ⋂ j ∈ (Finset.univ : Finset (Fin 1)),
      ZeroOneSet j) ⊆ {y : Fin 1 → ℝ | y 0 ≤ 1} := by
  apply convexHull_min
  · intro y hy
    have h2 := Set.mem_iInter₂.mp hy.2 0 (Finset.mem_univ 0)
    simp only [ZeroOneSet, Set.mem_setOf_eq] at h2
    simp only [Set.mem_setOf_eq]
    rcases h2 with h | h <;> rw [h] <;> norm_num
  · intro a ha c hc s u hs hu hsu
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hc ⊢
    nlinarith

open Disjunctive.HigherDim in
theorem solution : ¬ (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (Nprime S : Finset (Fin n)) (t : ℕ) (hS : S ⊆ Nprime) (hcard : S.card = t),
    KtSet A b Nprime t ⊆ convexHull ℝ (Poly A b ∩ ⋂ j ∈ S, ZeroOneSet j)) := by
  intro h
  have h1 := h (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 Finset.univ Finset.univ 1
    (Finset.Subset.refl _) (by simp)
  have h2 := hull_le_57229d57 (h1 kt_mem_57229d57)
  simp only [Set.mem_setOf_eq] at h2
  norm_num at h2
