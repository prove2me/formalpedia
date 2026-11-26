-- Prove2me | solution 1 for FourierJacobi.Analysis.polynomial_geometric_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:08.071529+00:00
-- url     : https://prove2.me/submissions/d8f08869-03f8-4923-9010-c90641b43d0e

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_Damping

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Analysis
open MeasureTheory Filter
open scoped Topology
namespace FourierJacobi.Analysis
theorem _root_.solution (k : ℕ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * r ^ n) := by
  exact summable_pow_mul_geometric_of_norm_lt_one k
    (by simpa [Real.norm_eq_abs, abs_of_nonneg hr₀] using hr₁)
end FourierJacobi.Analysis
