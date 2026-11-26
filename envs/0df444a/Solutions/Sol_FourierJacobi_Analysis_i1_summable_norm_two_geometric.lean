-- Prove2me | solution 1 for FourierJacobi.Analysis.i1_summable_norm_two_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:39.654033+00:00
-- url     : https://prove2.me/submissions/52410792-1fe0-4437-aa1a-ae23871fce7a

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
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
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable (fun n : ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2‖) := by
  have h := (geometric_norm_summable a ha).mul_norm (geometric_norm_summable b hb)
  simpa only [norm_mul, mul_assoc] using h.mul_left ‖C‖
end FourierJacobi.Analysis
