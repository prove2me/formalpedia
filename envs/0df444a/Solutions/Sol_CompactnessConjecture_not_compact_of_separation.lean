-- Prove2me | solution 1 for CompactnessConjecture.not_compact_of_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/ea3a932a-87a7-4a50-b1d7-f3a553dba5d8

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_extremalScale_pos

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Topology
namespace CompactnessConjecture
theorem _root_.solution
    {family : Finset FiniteGraph}
    (certificate : SeparationCertificate family) :
    ¬ IsCompactFamily family := by
  rintro ⟨forbidden, hmem, C, hC, hcomparison⟩
  have hepsilon : 0 < certificate.lowerConstant / (2 * C) := by
    exact div_pos certificate.lowerConstant_pos
      (mul_pos (by norm_num) hC)
  have hupper := certificate.family_littleO
    (certificate.lowerConstant / (2 * C)) hepsilon
  have hlower := certificate.member_lower forbidden hmem
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_gt_atTop 0
  have himpossible : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hupper, hlower, hcomparison, hpositive]
      with n hnupper hnlower hncomparison hnpositive
    have hs := extremalScale_pos hnpositive
    have hscaled :
        C * (familyExtremal family n : ℝ) ≤
          C * ((certificate.lowerConstant / (2 * C)) *
            extremalScale n) :=
      mul_le_mul_of_nonneg_left hnupper hC.le
    have hidentity :
        C * ((certificate.lowerConstant / (2 * C)) *
          extremalScale n) =
            (certificate.lowerConstant / 2) * extremalScale n := by
      field_simp
    rw [hidentity] at hscaled
    nlinarith [mul_pos certificate.lowerConstant_pos hs]
  exact himpossible.exists.elim (fun _ h => h)
end CompactnessConjecture
