-- Prove2me | solution 1 for ClassicalSchur.erL_five_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:41:44.595622+00:00
-- url     : https://prove2.me/submissions/1229b70f-70b6-4946-b571-f02d2252ad57

-- Generated from lean/ClassicalSchur/Values.lean
--   imports : 2 platform node(s), 3 definition bundle(s)
--   inlined : 3 file-scoped / sub-threshold helper(s)
--   rename  : erL_five_bounds -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Definitions.Def_ClassicalSchurValues
import Theorems.Thm_ClassicalSchur_erL_le
import Theorems.Thm_ClassicalSchur_le_erL_of_groupPartition
import Mathlib



namespace ClassicalSchur

theorem ramseyBound_four : ramseyBound 4 = 66 := by decide

theorem partitionZ7Z7_sumFree :
    ∀ i, ∀ x ∈ partitionZ7Z7 i, ∀ y ∈ partitionZ7Z7 i, x + y ∉ partitionZ7Z7 i := by
  decide

theorem partitionZ7Z7_cover : ∀ g : ZMod 7 × ZMod 7, g ≠ 0 → ∃ i, g ∈ partitionZ7Z7 i := by
  decide

end ClassicalSchur

open ClassicalSchur in
theorem solution : 49 ≤ erL 5 ∧ erL 5 ≤ 65 := by
  refine ⟨?_, ?_⟩
  · simpa using le_erL_of_groupPartition (n := 5) (m₁ := 7) (m₂ := 7) (by norm_num)
      (by norm_num) (by norm_num) (fun i => ↑(partitionZ7Z7 i))
      (fun i x hx y hy => partitionZ7Z7_sumFree i x hx y hy)
      (fun g hg => partitionZ7Z7_cover g hg)
  · simpa [ramseyBound_four] using erL_le 4
