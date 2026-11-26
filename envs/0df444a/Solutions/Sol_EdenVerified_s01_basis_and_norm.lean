-- Prove2me | solution 1 for EdenVerified.s01_basis_and_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:58.523664+00:00
-- url     : https://prove2.me/submissions/a19a117f-4924-4900-826b-2d922c303ac1

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_exteriorGrowthRate_basis
import Theorems.Thm_Eden_exteriorRate_eq_sum
import Theorems.Thm_Eden_norm_initialExteriorBasisVector
import Theorems.Thm_Eden_norm_sq_exteriorEvolution


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (p : PhaseSpace) (k : ℕ) :
    (∀ s : ExteriorIndex k, ‖initialExteriorBasisVector k p s‖ = 1 ∧
      exteriorGrowthRate k c p (initialExteriorBasisVector k p s) =
        ∑ j ∈ s.val, factorExponents c p j) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ v : ExteriorSpace k,
      ‖exteriorEvolution k c t p v‖ ^ 2 = ∑ s : ExteriorIndex k,
        (exteriorFactor k (derivativeFactors c t p) s *
          exteriorInitialCoordinates k p v s) ^ 2) := by
  constructor
  · intro s
    exact ⟨norm_initialExteriorBasisVector k p s,
      (exteriorGrowthRate_basis k c p s).trans (exteriorRate_eq_sum k c p s)⟩
  · exact fun t ht v => norm_sq_exteriorEvolution k c ht p v
end EdenVerified
