-- Prove2me | solution 1 for DetDLP.frobenius_isogeny_degree_quadratic_nonneg
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:31:45.175239+00:00
-- url     : https://prove2.me/submissions/dc3297c6-6a50-4a45-ae5f-a3fd13873a16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_quadratic_form_nonneg_iff_hasse_discriminant
import Theorems.Thm_DetDLP_section_2_3_5_primitive_machine_and_isogeny_axioms

set_option autoImplicit false

open DetDLP

/-- Proves `DetDLP.frobenius_isogeny_degree_quadratic_nonneg` from the directly proved
completing-the-square equivalence `DetDLP.quadratic_form_nonneg_iff_hasse_discriminant`
and the unified Section 2/3/5 specification
`DetDLP.section_2_3_5_primitive_machine_and_isogeny_axioms`. -/
theorem solution :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let N := Fintype.card E.toAffine.Point
        ∀ m n : ℤ, 0 ≤ m ^ 2 * (p : ℤ) - m * n * ((p : ℤ) + 1 - (N : ℤ)) + n ^ 2 := by
  intro p hp h3 E hEll
  letI := ecPointFintype E
  set N := Fintype.card E.toAffine.Point
  have hp_pos : (0 : ℤ) < (p : ℤ) := by omega
  have hdisc : ((N : ℤ) - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ) :=
    section_2_3_5_primitive_machine_and_isogeny_axioms.1
      quadratic_form_nonneg_iff_hasse_discriminant.2 p h3 E
  exact (quadratic_form_nonneg_iff_hasse_discriminant.2 (p : ℤ) (N : ℤ) hp_pos).mpr hdisc
