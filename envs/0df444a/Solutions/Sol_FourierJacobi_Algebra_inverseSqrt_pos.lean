-- Prove2me | solution 1 for FourierJacobi.Algebra.inverseSqrt_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:39.199375+00:00
-- url     : https://prove2.me/submissions/f37c0694-7dc5-48c7-8e6a-e8a09e3d4cdd

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
theorem _root_.solution {q : ℝ} (hq : 1 < q) : 0 < inverseSqrt q := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
end FourierJacobi.Algebra
