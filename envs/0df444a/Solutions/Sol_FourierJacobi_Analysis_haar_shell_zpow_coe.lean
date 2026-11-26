-- Prove2me | solution 1 for FourierJacobi.Analysis.haar_shell_zpow_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:36.038804+00:00
-- url     : https://prove2.me/submissions/b08b151d-e4af-4844-8b4b-66df83ef4c91

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Theorems.Thm_FourierJacobi_Analysis_inverseSqrt_even_zpow


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 0 ≤ q) (j : ℤ) :
    (q : ℂ) ^ (-j) = (inverseSqrt q : ℂ) ^ (2 * j) := by
  exact_mod_cast (inverseSqrt_even_zpow q hq j).symm
end FourierJacobi.Analysis
