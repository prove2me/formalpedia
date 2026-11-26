-- Prove2me | solution 1 for FourierJacobi.Analysis.depthMajorant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:24.060273+00:00
-- url     : https://prove2.me/submissions/feb03791-08ec-421e-b8cb-d9615fa32a94

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (c : ℕ) : 0 ≤ depthMajorant q c := by
  unfold depthMajorant
  positivity
end FourierJacobi.Analysis
