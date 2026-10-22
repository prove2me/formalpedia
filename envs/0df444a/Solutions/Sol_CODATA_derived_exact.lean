-- Prove2me | solution 1 for CODATA.derived_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:07:51.300892+00:00
-- url     : https://prove2.me/submissions/ac3e3970-bdc7-4476-bd06-a6c530d1102f

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values
/-!
# The exact derived constants of the 2022 adjustment

Because the 2019 revision of the International System of Units fixes
the exact values of the Planck constant h, the elementary charge e,
the Boltzmann constant k and the Avogadro constant N_A, a family of
derived quantities is exactly determined: the Josephson constant
K_J = 2e/h, the von Klitzing constant R_K = h/e², the magnetic flux
quantum Phi_0 = h/2e, the conductance quantum G_0 = 2e²/h and its
inverse, the Faraday constant F = N_A e, the molar gas constant
R = N_A k, the electronvolt, and the Planck constant in eV Hz⁻¹. The
2022 CODATA report prints these in Table XXXIII with the note
"exact" followed by further digits. This milestone verifies, by exact
rational arithmetic, that the values defined in `Def_CODATA_values`
lie in the rounding intervals determined by the printed digit
strings: K_J = 483 597.848 4 ... GHz V⁻¹, R_K = 25 812.807 45 ... Ω,
Phi_0 = 2.067 833 848 ... × 10⁻¹⁵ Wb, G_0 = 7.748 091 729 ... ×
10⁻⁵ S, G_0⁻¹ = 12 906.403 72 ... Ω, F = 96 485.332 12 ... C mol⁻¹,
R = 8.314 462 618 ... J mol⁻¹ K⁻¹, 1 eV = 1.602 176 634 × 10⁻¹⁹ J
exactly, and h = 4.135 667 696 ... × 10⁻¹⁵ eV Hz⁻¹. This milestone is
proved on the way to the goal theorem
`CODATA.codata_self_consistent`.
-/

open CODATA

/-- The exact derived constants determined by h, e, k and N_A agree
with the printed digit strings of Table XXXIII of the 2022 CODATA
report: K_J divided by 10^9 lies in [483597.8484, 483597.8485);
R_K lies in [25812.80745, 25812.80746); Phi_0 lies in
[2.067833848, 2.067833849) × 10⁻¹⁵; G_0 lies in
[7.748091729, 7.748091730) × 10⁻⁵; G_0⁻¹ lies in
[12906.40372, 12906.40373); F lies in [96485.33212, 96485.33213);
R lies in [8.314462618, 8.314462619); the electronvolt equals e
exactly; and h in eV Hz⁻¹ lies in [4.135667696, 4.135667697) ×
10⁻¹⁵. -/
theorem solution :
    4835978484/(10:ℚ)^4 ≤ kjVal/(10:ℚ)^9 ∧
      kjVal/(10:ℚ)^9 < 4835978485/(10:ℚ)^4 ∧
      2581280745/(10:ℚ)^5 ≤ rkVal ∧ rkVal < 2581280746/(10:ℚ)^5 ∧
      2067833848/(10:ℚ)^24 ≤ phi0Val ∧ phi0Val < 2067833849/(10:ℚ)^24 ∧
      7748091729/(10:ℚ)^14 ≤ g0Val ∧ g0Val < 7748091730/(10:ℚ)^14 ∧
      1290640372/(10:ℚ)^5 ≤ g0invVal ∧ g0invVal < 1290640373/(10:ℚ)^5 ∧
      9648533212/(10:ℚ)^5 ≤ faradayVal ∧
      faradayVal < 9648533213/(10:ℚ)^5 ∧
      8314462618/(10:ℚ)^9 ≤ gasVal ∧ gasVal < 8314462619/(10:ℚ)^9 ∧
      eVoltVal = 1602176634/(10:ℚ)^28 ∧
      4135667696/(10:ℚ)^24 ≤ h_eV ∧ h_eV < 4135667697/(10:ℚ)^24 := by
  simp only [kjVal, rkVal, phi0Val, g0Val, g0invVal, faradayVal, gasVal, eVoltVal, h_eV, hVal, eVal, kVal, naVal]
  norm_num


