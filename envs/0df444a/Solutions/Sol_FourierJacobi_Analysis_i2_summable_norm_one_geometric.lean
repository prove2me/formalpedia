-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_summable_norm_one_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:47.181802+00:00
-- url     : https://prove2.me/submissions/4f550380-7640-4aa7-8956-b01b4d8eead1

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Theorems.Thm_FourierJacobi_Analysis_geometric_norm_summable
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (C a : ℂ) (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ => ‖C * a ^ n‖) := by
  simpa only [norm_mul] using (geometric_norm_summable a ha).mul_left ‖C‖
end FourierJacobi.Analysis
