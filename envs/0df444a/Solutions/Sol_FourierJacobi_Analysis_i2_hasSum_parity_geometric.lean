-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_hasSum_parity_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:10:08.581991+00:00
-- url     : https://prove2.me/submissions/79e725fa-2b4a-4762-9c4c-2cc5de428f2c

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Theorems.Thm_FourierJacobi_Analysis_i2_summable_norm_parity_geometric
import Theorems.Thm_FourierJacobi_Analysis_hasSum_three_geometric
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
theorem _root_.solution (C z a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    HasSum (fun n : Fin 2 × ℕ × ℕ × ℕ =>
      C * z ^ n.1.val * a ^ n.2.1 * b ^ n.2.2.1 * c ^ n.2.2.2)
      (C * (1 + z) * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹) := by
  have hs := (i2_summable_norm_parity_geometric C z a b c ha hb hc).of_norm
  have hinner (e : Fin 2) :=
    (hasSum_three_geometric (C * z ^ e.val) a b c ha hb hc).tsum_eq
  have he : (∑' n : Fin 2 × ℕ × ℕ × ℕ,
      C * z ^ n.1.val * a ^ n.2.1 * b ^ n.2.2.1 * c ^ n.2.2.2) =
      C * (1 + z) * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [hinner, tsum_fintype, Fin.sum_univ_two, Fin.val_zero,
      Fin.val_one, pow_zero, pow_one]
    ring
  exact he ▸ hs.hasSum
end FourierJacobi.Analysis
