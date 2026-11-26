-- Prove2me | solution 1 for FirstPassageLinearTransport.cosh_booleanOptimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:27.233907+00:00
-- url     : https://prove2.me/submissions/c870c268-f357-474b-a3ae-a1dbf493788b

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_exp_booleanOptimizer
import Theorems.Thm_FirstPassageLinearTransport_exp_neg_booleanOptimizer
section
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
private theorem sqrt_ratio_average
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1) :
    (Real.sqrt (p / q) + Real.sqrt (q / p)) / 2 =
      1 / (2 * Real.sqrt (p * q)) := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  rw [Real.sqrt_div hp.le, Real.sqrt_div hq.le,
    Real.sqrt_mul hp.le]
  field_simp [ne_of_gt hsp, ne_of_gt hsq]
  rw [Real.sq_sqrt hp.le, Real.sq_sqrt hq.le, hpq]
end
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.cosh (booleanOptimizer t) =
      1 / (2 * Real.sqrt ((1 / 2 + t) * (1 / 2 - t))) := by
  have hq : 0 < (1 / 2 : ℝ) - t := by linarith
  have hp : 0 < (1 / 2 : ℝ) + t := by linarith
  rw [Real.cosh_eq, exp_booleanOptimizer ht0 ht1,
    exp_neg_booleanOptimizer ht0 ht1]
  exact sqrt_ratio_average hp hq (by ring)
end FirstPassageLinearTransport
