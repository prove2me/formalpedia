-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_collisionWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:59.949485+00:00
-- url     : https://prove2.me/submissions/8a22b543-3cdc-4125-b88d-c1bca9bbc30b

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_collisionProbability
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (r j h : ℤ)
    (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionWeight q r j h c‖) := by
  unfold collisionWeight
  split_ifs
  · simpa only [apply_ite, norm_one, norm_zero] using
      (hasSum_ite_eq (α := ℝ) (β := ℕ) 0 1).summable
  · exact summable_norm_collisionProbability q hq
end FourierJacobi.Analysis
