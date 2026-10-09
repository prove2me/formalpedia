-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.deriv_chi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:52:18.317092+00:00
-- url     : https://prove2.me/submissions/505b6ca2-078c-4801-a77b-b1d77fd1de14

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.deriv_chi_eq_zero
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_chi_eq_zero
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution {y : ℝ} (hy : 2 < |y|) : deriv chi y = 0 := by

  have hnb : chi =ᶠ[nhds y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with t ht
    exact chi_eq_zero (le_of_lt ht)
  exact ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hnb).deriv
