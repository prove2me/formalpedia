-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.schrodinger_exp_deficiency_trivial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:54:16.000099+00:00
-- url     : https://prove2.me/submissions/499dd377-a13c-4d8e-b62d-1047c3c96379

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.schrodinger_exp_deficiency_trivial
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_l2_classical_solution_eq_zero
import Theorems.Thm_BookProof_SchrodingerCutoff_Vexp_continuous
import Theorems.Thm_BookProof_SchrodingerCutoff_two_le_Vexp
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution
    (z : ℂ) (hz : z.re ≤ 1)
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x + (Vexp x : ℂ) * u x = z * u x)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 :=
  l2_classical_solution_eq_zero Vexp Vexp_continuous z u u' u'' h1 h2 heq
      (fun x => by linarith [two_le_Vexp x]) hL2
