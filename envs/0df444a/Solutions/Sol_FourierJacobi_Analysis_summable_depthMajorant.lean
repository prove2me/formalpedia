-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_depthMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:24.589583+00:00
-- url     : https://prove2.me/submissions/9dfd84ee-e1b8-4052-b8a8-7bf985298f63

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_collisionProbability

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (depthMajorant q) :=
  (hasSum_ite_eq (α := ℝ) (β := ℕ) 0 1).summable.add
    (summable_norm_collisionProbability q hq)
end FourierJacobi.Analysis
