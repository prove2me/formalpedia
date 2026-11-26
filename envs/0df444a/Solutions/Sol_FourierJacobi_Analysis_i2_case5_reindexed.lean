-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_case5_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:12:05.91068+00:00
-- url     : https://prove2.me/submissions/004fe2bd-881b-4cfb-802e-f7d071cdef13

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row0
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row0
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row0
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row1
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row1
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row1
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row2
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row2
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row2
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row3
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row3
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row3
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row4
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row4
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row4
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row5
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row5
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row5
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row6
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row6
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row6
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row7
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row7
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row7
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row8
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row8
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row8
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row9
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row9
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row9
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row10
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row10
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row10
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row11
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row11
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row11
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row12
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row12
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row12
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row13
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row13
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row13
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row14
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row14
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row14
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row15
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row15
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row15
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row16
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row16
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row16
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row17
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row17
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row17
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row18
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row18
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row18
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row19
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row19
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row19
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row20
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row20
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row20
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row21
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row21
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row21
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row22
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row22
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row22
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row23
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row23
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row23
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row24
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row24
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row24
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i2Case10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_i2Case5_cartan
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i2Case10Equiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero


attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row0
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row0
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row0
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row1
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row1
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row1
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row2
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row2
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row2
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row3
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row3
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row3
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row4
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row4
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row4
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row5
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row5
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row5
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row6
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row6
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row6
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row7
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row7
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row7
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row8
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row8
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row8
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row9
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row9
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row9
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row10
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row10
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row10
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row11
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row11
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row11
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row12
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row12
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row12
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row13
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row13
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row13
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row14
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row14
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row14
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row15
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row15
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row15
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row16
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row16
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row16
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row17
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row17
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row17
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row18
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row18
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row18
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row19
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row19
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row19
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row20
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row20
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row20
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row21
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row21
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row21
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row22
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row22
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row22
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row23
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row23
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row23
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row24
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row24
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row24

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 8 (i2Case5Equiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 7 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 8) * (d * T * V * t) ^ n.1 * (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row8]
  unfold shellMonomial
  rw [i2Case5_cartan]
  simp only [i2Case5Equiv_val]
  have he : 3 * ((n.1 : ℤ)+1) + 2 * (-2*((n.1 : ℤ)+1)-(n.2.1 : ℤ)-1) + 2 * (-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-2) + 3 * (-2*((n.1 : ℤ)+1)-2*(-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-2)) + 4 * (((n.1 : ℤ)+1)) = ((n.1 + 2 * n.2.1 + 4 * n.2.2 + 7 : ℕ) : ℤ) := by omega
  have hn : (-2*((n.1 : ℤ)+1)-2*(-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-2)) / 2 = ((n.2.1 + n.2.2 + 2 : ℕ) : ℤ) := by omega
  have hb : (((n.1 : ℤ)+1)) = ((n.1 + 1 : ℕ) : ℤ) := by omega
  have hk : (n.1 : ℤ)+1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring
end FourierJacobi.Analysis
