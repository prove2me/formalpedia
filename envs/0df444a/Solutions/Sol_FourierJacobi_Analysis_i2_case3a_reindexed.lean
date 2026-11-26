-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_case3a_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:10:49.941106+00:00
-- url     : https://prove2.me/submissions/fe41cc85-3f6b-452f-8499-607c81fc2bda

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
import Theorems.Thm_FourierJacobi_Analysis_i2Case3a_cartan
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
theorem _root_.solution (q t d U V T : ℂ) (n : Fin 2 × ℕ × ℕ × ℕ) :
    i2SpatialTerm q t d U V T 3 (i2Case3aEquiv n).val =
      (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 0 * i2DepthMass q 3) * (T * V * t ^ 2) ^ n.1.val * (d * T * V * t) ^ n.2.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.2.1 * (t ^ 2) ^ n.2.2.2 := by
  unfold i2SpatialTerm
  rw [i2DepthAt_row3]
  unfold shellMonomial
  rw [i2Case3a_cartan]
  simp only [i2Case3aEquiv_val]
  have he : 3 * ((n.2.1 : ℤ)+1) + 2 * (-2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1) + 2 * (-((n.2.1 : ℤ)+1)-(n.2.2.1 : ℤ)-1+(n.2.2.2 : ℤ)) + 3 * (4) + 4 * (-((n.2.1 : ℤ)+1)-(-2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1)-2) = ((n.2.1 + 2 * n.2.2.1 + 2 * n.2.2.2 + 2 * n.1.val + 5 : ℕ) : ℤ) := by omega
  have hn : (4) / 2 = ((2 : ℕ) : ℤ) := by omega
  have hb : (-((n.2.1 : ℤ)+1)-(-2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1)-2) = ((n.2.1 + 2 * n.2.2.1 + n.1.val : ℕ) : ℤ) := by omega
  have hk : (n.2.1 : ℤ)+1 = ((n.2.1 + 1 : ℕ) : ℤ) := by omega
  rw [he]
  try rw [hn]
  try rw [hb]
  try rw [hk]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_zero, pow_one, inv_pow, div_eq_mul_inv]
  ring
end FourierJacobi.Analysis
