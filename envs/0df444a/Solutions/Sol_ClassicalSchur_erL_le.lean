-- Prove2me | solution 1 for ClassicalSchur.erL_le
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:29:28.754856+00:00
-- url     : https://prove2.me/submissions/938318eb-5d45-41e2-9cb2-748d7dca63a5

-- Generated from lean/ClassicalSchur/Ramsey.lean
--   imports : 1 platform node(s), 2 definition bundle(s)
--   inlined : 2 file-scoped / sub-threshold helper(s)
--   rename  : erL_le -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_le_sdeg_blockSums
import Mathlib



namespace ClassicalSchur

/-- The property of ER Definition 5.1 holds at every length `L` with
`ramseyBound k ≤ L + 1`, whatever the average. -/
theorem erProperty_of_ramseyBound (k L : ℕ) (hL : ramseyBound k ≤ L + 1) :
    ERProperty (k + 1) L := by
  intro A hlen _ _
  exact le_sdeg_blockSums (by omega)

theorem two_le_ramseyBound (k : ℕ) : 2 ≤ ramseyBound k := by
  cases k <;> simp [ramseyBound]

end ClassicalSchur

open ClassicalSchur in
theorem solution (k : ℕ) : erL (k + 1) ≤ ramseyBound k - 1 := by
  have h2 := two_le_ramseyBound k
  exact Nat.sInf_le ⟨by omega, erProperty_of_ramseyBound k _ (by omega)⟩
