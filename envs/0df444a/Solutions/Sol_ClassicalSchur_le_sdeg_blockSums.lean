-- Prove2me | solution 1 for ClassicalSchur.le_sdeg_blockSums
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:27:57.481089+00:00
-- url     : https://prove2.me/submissions/21cc4638-3850-4ff0-83ae-51d1e3bedba8

-- Generated from lean/ClassicalSchur/Ramsey.lean
--   imports : 2 platform node(s), 2 definition bundle(s)
--   inlined : 1 file-scoped / sub-threshold helper(s)
--   rename  : le_sdeg_blockSums -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_not_coveredBySumFree_blockSums
import Theorems.Thm_ClassicalSchur_triangleRamsey_ramseyBound
import Mathlib



namespace ClassicalSchur

/-- If no cover by fewer than `n` sumfree sets exists, then `sdeg X ≥ n`. -/
theorem le_sdeg_of_forall_not_covered {X : Set ℕ} {n : ℕ}
    (h : ∀ q, 1 ≤ q → q < n → ¬ CoveredBySumFree X q) : (n : ℕ∞) ≤ sdeg X := by
  refine le_sInf ?_
  rintro _ ⟨q, ⟨hq1, hq⟩, rfl⟩
  by_contra! hlt
  exact h q hq1 (by exact_mod_cast hlt) hq

end ClassicalSchur

open ClassicalSchur in
theorem solution {k : ℕ} {A : List ℕ} (hA : ramseyBound k ≤ A.length + 1) :
    ((k + 1 : ℕ) : ℕ∞) ≤ sdeg (blockSums A) :=
  le_sdeg_of_forall_not_covered fun _ _ hq =>
    not_coveredBySumFree_blockSums (triangleRamsey_ramseyBound k) hA (by omega)
