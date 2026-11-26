-- Prove2me | solution 1 for FourierJacobi.Algebra.inverseSqrt_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:40.041487+00:00
-- url     : https://prove2.me/submissions/71f1c42b-4a1c-4ee3-b380-c8da7b96c6e3

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
theorem _root_.solution {q : ℝ} (hq : 1 < q) : inverseSqrt q < 1 := by
  have hs : 1 < Real.sqrt q := by
    have h := Real.sq_sqrt (show 0 ≤ q by linarith)
    have hnon := Real.sqrt_nonneg q
    nlinarith
  exact (inv_lt_one₀ (by linarith : 0 < Real.sqrt q)).mpr hs
end FourierJacobi.Algebra
