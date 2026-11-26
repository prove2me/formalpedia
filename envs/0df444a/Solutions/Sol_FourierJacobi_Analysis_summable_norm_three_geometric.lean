-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_three_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:00.594291+00:00
-- url     : https://prove2.me/submissions/39e834f6-9603-433b-9997-c7acf5b560f7

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_geometric_norm_summable

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (C a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    Summable (fun n : ℕ × ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2‖) := by
  have hBC := (geometric_norm_summable b hb).mul_norm (geometric_norm_summable c hc)
  have hABC := (geometric_norm_summable a ha).mul_norm hBC
  simpa only [norm_mul, mul_assoc] using hABC.mul_left ‖C‖
end FourierJacobi.Analysis
