-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.factorial_denominator_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:18:35.852216+00:00
-- url     : https://prove2.me/submissions/276693c5-4a27-4ece-8c53-42dcbc8dc126

import Theorems.Thm_EulerMascheroni_Arithmetic_no_small_integral_pade_forms
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_normalized_form_integral
open EulerMascheroni.Arithmetic

theorem solution (a : ℝ) (ha : IsAlgebraic ℚ a) :
    ¬ EulerMascheroni.Arithmetic.ExponentialDenominators a := by
  rintro ⟨C, hC, h⟩
  choose d hdpos hdle hdi using h
  apply no_small_integral_pade_forms a ha C hC (fun n => d (2*n))
    (fun n => hdpos (2*n)) (fun n => hdle (2*n))
  intro n
  exact pade_normalized_form_integral a n (d (2*n)) (hdi (2*n))

#print axioms solution
