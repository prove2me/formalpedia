-- Prove2me | solution 1 for CODATA.alpha_family
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:07:33.781771+00:00
-- url     : https://prove2.me/submissions/ae5e1323-a77a-4e36-a09c-6a8f1b1d2750

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values
/-!
# A single relative-uncertainty witness for the alpha family

In the 2022 CODATA adjustment the vacuum magnetic permeability, the
vacuum electric permittivity, the impedance of vacuum and the two
fine-structure-constant entries form a family: mu_0 = 2 alpha h/(e² c),
eps_0, Z_0 and alpha are mutually determined, the other factors being
exact. Their printed uncertainties in Table XXXIII (two significant
digits) are therefore all products of a single relative uncertainty
with the respective exact values: alpha = 7.297 352 5643(11) × 10⁻³,
1/alpha = 137.035 999 177(21), mu_0 = 1.256 637 061 27(20) × 10⁻⁶,
eps_0 = 8.854 187 8188(14) × 10⁻¹², Z_0 = 376.730 313 412(58). This
milestone verifies the consistency of these five printed uncertainty
statements by exact rational arithmetic: there is a single rational
relative-uncertainty witness ur, of order 1.6 × 10⁻¹⁰, such that ur
times each of the five rational values lies in the rounding interval
determined by the printed two-digit uncertainty. This milestone is
proved on the way to the goal theorem
`CODATA.codata_self_consistent`.
-/

open CODATA

/-- There is a single rational relative uncertainty ur with
1.55 × 10⁻¹⁰ ≤ ur < 1.65 × 10⁻¹⁰ such that ur alpha lies in
[1.05, 1.15) × 10⁻¹², ur/alpha lies in [2.05, 2.15) × 10⁻⁸,
ur mu_0 lies in [1.95, 2.05) × 10⁻¹⁶, ur eps_0 lies in
[1.35, 1.45) × 10⁻²¹ and ur Z_0 lies in [5.85, 5.95) × 10⁻⁸: one
witness reproduces the printed two-significant-digit uncertainties of
the whole alpha family of the 2022 adjustment. -/
theorem solution :
    ∃ ur : ℚ,
      155/(10:ℚ)^12 ≤ ur ∧ ur < 165/(10:ℚ)^12 ∧
      105/(10:ℚ)^14 ≤ ur * alphaVal ∧ ur * alphaVal < 115/(10:ℚ)^14 ∧
      205/(10:ℚ)^10 ≤ ur * alphaInvVal ∧
      ur * alphaInvVal < 215/(10:ℚ)^10 ∧
      195/(10:ℚ)^18 ≤ ur * mu0Val ∧ ur * mu0Val < 205/(10:ℚ)^18 ∧
      135/(10:ℚ)^23 ≤ ur * eps0Val ∧ ur * eps0Val < 145/(10:ℚ)^23 ∧
      585/(10:ℚ)^10 ≤ ur * z0Val ∧ ur * z0Val < 595/(10:ℚ)^10 := by
  refine ⟨156/(10:ℚ)^12, ?_⟩
  simp only [alphaVal, alphaInvVal, mu0Val, eps0Val, z0Val]
  norm_num


