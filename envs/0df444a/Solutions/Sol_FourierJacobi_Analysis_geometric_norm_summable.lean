-- Prove2me | solution 1 for FourierJacobi.Analysis.geometric_norm_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:26.354607+00:00
-- url     : https://prove2.me/submissions/be056b43-49fa-4a18-970b-d14a13a629e4

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖z ^ n‖) := by
  have hz' : ‖(‖z‖ : ℝ)‖ < 1 := by simpa using hz
  simpa only [norm_pow] using (hasSum_geometric_of_norm_lt_one hz').summable
end FourierJacobi.Analysis
