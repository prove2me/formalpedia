-- Prove2me | solution 1 for DiscreteExpectation.partition_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:14:09.008498+00:00
-- url     : https://prove2.me/submissions/dd9dbe88-94dc-4cfa-be0a-a34d04614409

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
noncomputable section

theorem solution {a b : ℝ} (P : Partition a b) (F : ℝ → ℝ) :
    ∑ i : Fin P.n, (F (P.pts i.succ) - F (P.pts i.castSucc)) = F b - F a := by
  let g : ℕ → ℝ := fun i => if h : i < P.n + 1 then F (P.pts ⟨i, h⟩) else 0

  have h_sum : ∑ i : Fin P.n, (F (P.pts i.succ) - F (P.pts i.castSucc)) =
               ∑ i ∈ Finset.range P.n, (g (i + 1) - g i) := by
    apply Finset.sum_bij (fun (i : Fin P.n) _ => i.val)
    · -- 1. hi (mapped elements are in the target finset)
      intro k _
      exact Finset.mem_range.mpr k.isLt
    · -- 2. i_inj (the mapping is injective)
      intro a1 _ a2 _ h
      exact Fin.ext h
    · -- 3. i_surj (the mapping is surjective)
      intro b hb
      refine ⟨⟨b, Finset.mem_range.mp hb⟩, Finset.mem_univ _, rfl⟩
    · -- 4. h (the terms are equal)
      intro k _
      have h1 : k.val + 1 < P.n + 1 := Nat.succ_lt_succ k.isLt
      have h2 : k.val < P.n + 1 := Nat.lt_succ_of_lt k.isLt

      -- Explicitly change the goal to the unfolded version of `g`
      change F (P.pts k.succ) - F (P.pts k.castSucc) =
        (if h : k.val + 1 < P.n + 1 then F (P.pts ⟨k.val + 1, h⟩) else 0) -
        (if h : k.val < P.n + 1 then F (P.pts ⟨k.val, h⟩) else 0)

      rw [dif_pos h1, dif_pos h2]
      congr

  rw [h_sum, Finset.sum_range_sub]
  have hn : P.n < P.n + 1 := Nat.lt_succ_self P.n
  have h0 : 0 < P.n + 1 := Nat.succ_pos P.n

  -- Explicitly change the goal to the unfolded version of `g`
  change (if h : P.n < P.n + 1 then F (P.pts ⟨P.n, h⟩) else 0) -
         (if h : 0 < P.n + 1 then F (P.pts ⟨0, h⟩) else 0) = F b - F a

  rw [dif_pos hn, dif_pos h0]
  have eq_b : F (P.pts ⟨P.n, hn⟩) = F b := by
    have : (⟨P.n, hn⟩ : Fin (P.n + 1)) = Fin.last P.n := Fin.ext rfl
    rw [this, P.pts_end]
  have eq_a : F (P.pts ⟨0, h0⟩) = F a := by
    have : (⟨0, h0⟩ : Fin (P.n + 1)) = 0 := Fin.ext rfl
    rw [this, P.pts_start]
  rw [eq_b, eq_a]
