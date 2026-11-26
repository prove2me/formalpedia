-- Prove2me | solution 1 for FourierJacobi.Analysis.haar_scale_rpow_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:47.396674+00:00
-- url     : https://prove2.me/submissions/e5dae507-df8e-44af-ae0a-71243634809c

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Theorems.Thm_FourierJacobi_Analysis_haar_scale_rpow

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 0 < q) (k : ℤ) :
    (Real.rpow (q ^ (-k)) (3 / 2) : ℂ) = (inverseSqrt q : ℂ) ^ (3 * k) := by
  rw [haar_scale_rpow q hq]
  exact Complex.ofReal_zpow _ _
end FourierJacobi.Analysis
