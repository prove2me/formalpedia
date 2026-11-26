-- Prove2me | solution 1 for FourierJacobi.Algebra.inverseSqrt_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:53.803526+00:00
-- url     : https://prove2.me/submissions/0e3a8dfa-2dc3-4e33-b49a-f0bb2578957d

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
theorem _root_.solution {q : ℝ} (hq : 0 ≤ q) : inverseSqrt q ^ 2 = q⁻¹ := by
  rw [inverseSqrt, inv_pow, Real.sq_sqrt hq]
end FourierJacobi.Algebra
