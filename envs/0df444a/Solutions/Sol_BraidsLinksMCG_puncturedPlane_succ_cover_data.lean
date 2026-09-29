-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlane_succ_cover_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T06:32:42.445985+00:00
-- url     : https://prove2.me/submissions/8c25421f-702c-4edb-bb65-a1a0deb496ec

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open BraidsLinksMCG

theorem solution (n : ℕ) :
    ∃ A : Fin 2 → Set (PuncturedPlane (n + 1)),
      A 0 = {z : PuncturedPlane (n + 1) |
        (1 / 4 : ℝ) < dist (z : ℂ) (((n : ℕ) + 1 : ℕ) : ℂ)} ∧
      A 1 = {z : PuncturedPlane (n + 1) |
        dist (z : ℂ) ((((n : ℕ) + 1 : ℕ) : ℂ) + (1 / 2 : ℂ)) < (1 : ℝ)} ∧
      (∀ b : Fin 2, basePunctured (n + 1) ∈ A b) ∧
      (∀ b : Fin 2, IsOpen (A b)) ∧
      Set.iUnion A = (Set.univ : Set (PuncturedPlane (n + 1))) := by
  let p : ℂ := (((n : ℕ) + 1 : ℕ) : ℂ)
  let U : Set (PuncturedPlane (n + 1)) :=
    {z | (1 / 4 : ℝ) < dist (z : ℂ) p}
  let V : Set (PuncturedPlane (n + 1)) :=
    {z | dist (z : ℂ) (p + (1 / 2 : ℂ)) < (1 : ℝ)}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const (continuous_subtype_val.dist continuous_const)
  have hVopen : IsOpen V := by
    dsimp [V]
    exact isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
  have hbase0 : basePunctured (n + 1) ∈ U := by
    apply Set.mem_setOf.2
    norm_num [U, basePunctured, dist_eq_norm, p]
  have hbase1 : basePunctured (n + 1) ∈ V := by
    apply Set.mem_setOf.2
    norm_num [V, basePunctured, dist_eq_norm, p]
  have hcenter : dist p (p + (1 / 2 : ℂ)) = (1 / 2 : ℝ) := by
    rw [dist_eq_norm]
    norm_num [p, add_sub_cancel_left]
  have hcover : Set.iUnion (![U, V] : Fin 2 → Set (PuncturedPlane (n + 1))) =
      (Set.univ : Set (PuncturedPlane (n + 1))) := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : (1 / 4 : ℝ) < dist (z : ℂ) p
    · exact Set.mem_iUnion.mpr ⟨0, hz⟩
    · have hz' : dist (z : ℂ) p ≤ (1 / 4 : ℝ) := le_of_not_gt hz
      apply Set.mem_iUnion.mpr
      refine ⟨1, ?_⟩
      apply Set.mem_setOf.2
      have htri' :
          dist (z : ℂ) (p + (1 / 2 : ℂ)) ≤ (3 / 4 : ℝ) := by
        calc
          dist (z : ℂ) (p + (1 / 2 : ℂ)) ≤
              dist (z : ℂ) p + dist p (p + (1 / 2 : ℂ)) :=
            dist_triangle (z : ℂ) p (p + (1 / 2 : ℂ))
          _ ≤ dist (z : ℂ) p + (1 / 2 : ℝ) := by rw [hcenter]
          _ ≤ (1 / 4 : ℝ) + (1 / 2 : ℝ) := by
            simpa [add_comm] using
              (add_le_add_right hz' (1 / 2 : ℝ))
          _ = (3 / 4 : ℝ) := by norm_num
      exact lt_of_le_of_lt htri' (by norm_num)
  have hA :
      (![U, V] : Fin 2 → Set (PuncturedPlane (n + 1))) 0 =
        {z : PuncturedPlane (n + 1) |
          (1 / 4 : ℝ) < dist (z : ℂ) (((n : ℕ) + 1 : ℕ) : ℂ)} := by
    apply Set.ext
    intro z
    simp [U, p, Nat.cast_add, Nat.cast_one]
  have hB :
      (![U, V] : Fin 2 → Set (PuncturedPlane (n + 1))) 1 =
        {z : PuncturedPlane (n + 1) |
          dist (z : ℂ)
            ((((n : ℕ) + 1 : ℕ) : ℂ) + (1 / 2 : ℂ)) < (1 : ℝ)} := by
    apply Set.ext
    intro z
    simp [V, p, Nat.cast_add, Nat.cast_one]
  refine ⟨![U, V], hA, hB, ?_, ?_, hcover⟩
  · intro b
    fin_cases b
    · exact hbase0
    · exact hbase1
  · intro b
    fin_cases b
    · exact hUopen
    · exact hVopen
