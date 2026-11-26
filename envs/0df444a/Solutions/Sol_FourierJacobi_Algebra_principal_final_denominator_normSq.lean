-- Prove2me | solution 1 for FourierJacobi.Algebra.principal_final_denominator_normSq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:38.558831+00:00
-- url     : https://prove2.me/submissions/2280dfc8-9f6f-4e5a-a27f-1bb18754d71d

import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {t : ℝ} {d : ℂ} (hd : ‖d‖ = 1) :
    (1 + d * (t : ℂ)) * (1 + (t : ℂ) / d) =
      (Complex.normSq (1 + d * (t : ℂ)) : ℂ) := by
  rw [← Complex.mul_conj]
  congr 1
  simp [div_eq_mul_inv, Complex.inv_eq_conj hd, mul_comm]
end FourierJacobi.Algebra
