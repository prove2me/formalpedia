-- Prove2me | solution 1 for FourierJacobi.Analysis.paperE_eq_closedCore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:30.623505+00:00
-- url     : https://prove2.me/submissions/2f7980ae-c1d2-4012-bcbb-f89f7140ca03

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Analysis_inverseSqrt_coe_sq
import Theorems.Thm_FourierJacobi_Analysis_paperC_eq_poincare
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 0 ≤ q) (a b d : ℂ) :
    paperE q a b d = closedCore (inverseSqrt q : ℂ) a b d := by
  unfold paperE closedCore satakeNumerator n₁ n₂ d₁ d₂ fourFactors
  rw [← paperC_eq_poincare q hq, inverseSqrt_coe_sq q hq]
  simp only [paperN1, paperN2, paperD1, paperD2, satakeTuple,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one, div_eq_mul_inv, mul_inv_rev]
  ring
end FourierJacobi.Analysis
