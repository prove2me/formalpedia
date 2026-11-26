-- Prove2me | solution 1 for FourierJacobi.Analysis.i1_hasSum_two_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:44.002535+00:00
-- url     : https://prove2.me/submissions/f475bc52-b35f-4827-b31f-ed82132e0e28

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1_summable_norm_two_geometric
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
    HasSum (fun n : ℕ × ℕ => C * a ^ n.1 * b ^ n.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹) := by
  have hA := (hasSum_geometric_of_norm_lt_one ha).tsum_eq
  have hB := (hasSum_geometric_of_norm_lt_one hb).tsum_eq
  have hs := (i1_summable_norm_two_geometric C a b ha hb).of_norm
  have he : (∑' n : ℕ × ℕ, C * a ^ n.1 * b ^ n.2) =
      C * (1 - a)⁻¹ * (1 - b)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [tsum_mul_left, hB, tsum_mul_right, hA]
  exact he ▸ hs.hasSum
end FourierJacobi.Analysis
