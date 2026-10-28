-- Prove2me | solution 1 for CountingMatroid.Analysis.RankWeightClosurePair.rank_weight_closure_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:44:59.914374+00:00
-- url     : https://prove2.me/submissions/58a303d4-6d24-45a4-bac8-15faa388f481

import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Tactic

namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
section


set_option autoImplicit false

/-! Rank increments identify the exact normalized coefficient of a pair of
labels: a pair of nonloops in the same closure class receives the factor q,
and every other pair receives the factor one. -/

namespace CountingMatroid.Analysis.RankWeightClosurePair
open scoped Classical

/-- INTERNAL: In a full-ground finite matroid, inserting a label increments
rank exactly when the label is outside the closure. -/
theorem rank_insert_toNat {α : Type} [Finite α]
    (N : Matroid α) (hfull : N.E = Set.univ) (X : Set α) (a : α) :
    (N.eRk (insert a X)).toNat = (N.eRk X).toNat +
      if a ∈ N.closure X then 0 else 1 := by
  classical
  by_cases ha : a ∈ N.closure X
  · rw [if_pos ha, add_zero, ← N.eRk_closure_eq (insert a X),
      N.closure_insert_eq_of_mem_closure ha, N.eRk_closure_eq]
  · rw [if_neg ha, N.eRk_insert_eq_add_one ⟨by simp [hfull], ha⟩,
      ENat.toNat_add (N.isRkFinite_set X).eRk_lt_top.ne (by simp)]
    rfl



end CountingMatroid.Analysis.RankWeightClosurePair

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · derived singleton rank increments from closure and the exact pair discount from closure exchange; no Lorentzian certificate is assumed.
-/

end
set_option autoImplicit false

/-! Rank increments identify the exact normalized coefficient of a pair of
labels: a pair of nonloops in the same closure class receives the factor q,
and every other pair receives the factor one. -/

namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightClosurePair
open scoped Classical

/-- INTERNAL: Rank-weight pair coefficients are products of singleton
increments, discounted precisely on equal nonloop closure classes.
TEXLINE: main.tex:334-348 -/
theorem solution {α : Type} [Finite α]
    (N : Matroid α) (hfull : N.E = Set.univ) (X : Set α)
    (q : ℚ) (hq : 0 < q) (a b : α) :
    (q ^ (N.eRk (insert a (insert b X))).toNat)⁻¹ *
      (q ^ (N.eRk X).toNat)⁻¹ =
      (if a ∉ N.closure X ∧ b ∉ N.closure X ∧
          N.closure (insert a X) = N.closure (insert b X) then q else 1) *
        (q ^ (N.eRk (insert a X)).toNat)⁻¹ *
        (q ^ (N.eRk (insert b X)).toNat)⁻¹ := by
  classical
  have hq0 : q ≠ 0 := ne_of_gt hq
  have ha_ground : a ∈ N.E := by simp [hfull]
  have hb_ground : b ∈ N.E := by simp [hfull]
  by_cases ha : a ∈ N.closure X
  · have hax : a ∈ N.closure (insert b X) :=
      N.closure_subset_closure (Set.subset_insert b X) ha
    rw [rank_insert_toNat N hfull X a, rank_insert_toNat N hfull (insert b X) a]
    simp [ha, hax, mul_comm]
  · by_cases hb : b ∈ N.closure X
    · have hcl := N.closure_insert_eq_of_mem_closure hb
      have hr : (N.eRk (insert a (insert b X))).toNat =
          (N.eRk (insert a X)).toNat := by
        rw [← N.eRk_closure_eq (insert a (insert b X)),
          N.closure_insert_congr_right hcl, N.eRk_closure_eq]
      rw [hr, rank_insert_toNat N hfull X b]
      simp [hb]
    · by_cases hc : N.closure (insert a X) = N.closure (insert b X)
      · have hab : a ∈ N.closure (insert b X) :=
          hc ▸ N.mem_closure_of_mem' (Set.mem_insert a X) ha_ground
        rw [rank_insert_toNat N hfull (insert b X) a,
          rank_insert_toNat N hfull X a, rank_insert_toNat N hfull X b]
        simp only [if_pos hab, if_neg ha, if_neg hb, add_zero,
          if_pos (show a ∉ N.closure X ∧ b ∉ N.closure X ∧
            N.closure (insert a X) = N.closure (insert b X) from ⟨ha, hb, hc⟩)]
        rw [pow_succ]
        field_simp
      · have hab : a ∉ N.closure (insert b X) := by
          intro h
          exact hc (N.closure_insert_congr ⟨h, ha⟩)
        rw [rank_insert_toNat N hfull (insert b X) a,
          rank_insert_toNat N hfull X a, rank_insert_toNat N hfull X b]
        simp only [if_neg hab, if_neg ha, if_neg hb,
          if_neg (show ¬ (a ∉ N.closure X ∧ b ∉ N.closure X ∧
            N.closure (insert a X) = N.closure (insert b X)) from fun h => hc h.2.2),
          one_mul]
        simp only [pow_succ, mul_inv_rev]
        ring
