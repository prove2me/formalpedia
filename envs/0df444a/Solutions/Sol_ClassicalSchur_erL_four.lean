-- Prove2me | solution 1 for ClassicalSchur.erL_four
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:32:41.171608+00:00
-- url     : https://prove2.me/submissions/b4d4e937-3b7d-41ad-b5c6-421a3fd4c560

-- Generated from lean/ClassicalSchur/Values.lean
--   imports : 2 platform node(s), 2 definition bundle(s)
--   inlined : 3 file-scoped / sub-threshold helper(s)
--   rename  : erL_four -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_le_sdeg_blockSums
import Theorems.Thm_ClassicalSchur_not_erProperty_four
import Mathlib



namespace ClassicalSchur

/-- The property of ER Definition 5.1 holds at every length `L` with
`ramseyBound k ≤ L + 1`, whatever the average. -/
theorem erProperty_of_ramseyBound (k L : ℕ) (hL : ramseyBound k ≤ L + 1) :
    ERProperty (k + 1) L := by
  intro A hlen _ _
  exact le_sdeg_blockSums (by omega)

theorem ramseyBound_three : ramseyBound 3 = 17 := by decide

/-- The property of ER Definition 5.1 holds at `n = 4`, `L = 16`. -/
theorem erProperty_four_sixteen : ERProperty 4 16 :=
  erProperty_of_ramseyBound 3 16 (by rw [ramseyBound_three])

end ClassicalSchur

open ClassicalSchur in
theorem solution : erL 4 = 16 := by
  refine IsLeast.csInf_eq ⟨⟨by norm_num, erProperty_four_sixteen⟩, ?_⟩
  rintro L ⟨h0, hP⟩
  by_contra h
  exact not_erProperty_four h0 (by omega) hP
