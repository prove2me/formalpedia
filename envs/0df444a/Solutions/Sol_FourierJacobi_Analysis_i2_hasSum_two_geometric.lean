-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_hasSum_two_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:43:27.435295+00:00
-- url     : https://prove2.me/submissions/7deff243-a992-48a9-b9f1-3403d49ac88a

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Theorems.Thm_FourierJacobi_Analysis_i2_summable_norm_two_geometric
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
theorem _root_.solution (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (fun n : ℕ × ℕ => C * a ^ n.1 * b ^ n.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹) := by
  have hs := (i2_summable_norm_two_geometric C a b ha hb).of_norm
  have hA := (hasSum_geometric_of_norm_lt_one ha).tsum_eq
  have hB := (hasSum_geometric_of_norm_lt_one hb).tsum_eq
  have he : (∑' n : ℕ × ℕ, C * a ^ n.1 * b ^ n.2) =
      C * (1 - a)⁻¹ * (1 - b)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [tsum_mul_left, hB, tsum_mul_right, hA]
  exact he ▸ hs.hasSum
end FourierJacobi.Analysis
