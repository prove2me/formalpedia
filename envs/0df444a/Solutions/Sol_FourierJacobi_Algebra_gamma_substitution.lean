-- Prove2me | solution 1 for FourierJacobi.Algebra.gamma_substitution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:46.833542+00:00
-- url     : https://prove2.me/submissions/6ab91e78-e579-4d0c-8646-44e884b832a0

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (a b gamma : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hgamma : a * b * gamma ^ 2 = 1) (i : Fin 8) :
    gamma ^ 2 * weylL a b i ^ 2 = weylU a b i := by
  have hg : gamma ^ 2 = (a * b)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff (mul_ne_zero ha hb)).mpr
    simpa [mul_comm] using hgamma
  rw [hg]
  fin_cases i <;> simp [weylL, weylU] <;> field_simp
end FourierJacobi.Algebra
