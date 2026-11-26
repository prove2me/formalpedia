-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_summable_norm_parity_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:50.776181+00:00
-- url     : https://prove2.me/submissions/864b59b7-c265-4813-9fd5-c69e8e140f85

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_three_geometric


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (C z a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    Summable (fun n : Fin 2 × ℕ × ℕ × ℕ =>
      ‖C * z ^ n.1.val * a ^ n.2.1 * b ^ n.2.2.1 * c ^ n.2.2.2‖) := by
  have hz : Summable (fun e : Fin 2 => ‖z ^ e.val‖) := (hasSum_fintype _).summable
  have h := hz.mul_norm (summable_norm_three_geometric C a b c ha hb hc)
  convert h using 1
  funext n
  congr 1
  ring
end FourierJacobi.Analysis
