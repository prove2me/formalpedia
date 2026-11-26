-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i2_case3b_regionTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:03.214515+00:00
-- url     : https://prove2.me/submissions/e782aeb6-b90e-4ba5-b49a-6ce371c9d183

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
import Theorems.Thm_FourierJacobi_Analysis_i2_case3b_reindexed
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i2Case10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_i2_geometric_denominator_ne
import Theorems.Thm_FourierJacobi_Analysis_i2_hasSum_two_geometric
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
theorem _root_.solution (q t d U V T : ℂ)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0)
    (hQ : ‖t ^ 2‖ < 1)
    (hP : ‖d * T * V * t‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    : HasSum (fun p : I2SpatialRow 4 => i2SpatialTerm q t d U V T 4 p.val)
      (i2RegionTerm 4 t d (T * U) (T * V)) := by
  have h := i2_hasSum_two_geometric (-q * (1 - t ^ 2) ^ 2 * (d ^ 1) * t ^ 5 * (T * U) ^ 2 * (T * V) ^ 1 * i2DepthMass q 4) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) hP hE
  apply i2Case3bEquiv.hasSum_iff.mp
  convert h using 1
  · exact funext fun n => i2_case3b_reindexed q t d U V T n
  · have ht : t ≠ 0 := by
      intro ht
      simp [ht] at hq
    have hqeq : q = (t ^ 2)⁻¹ := by
      calc
        q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
        _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hq, one_mul]
    have hnQ := i2_geometric_denominator_ne (t ^ 2) hQ
    have hnP := i2_geometric_denominator_ne (d * T * V * t) hP
    have hnE := i2_geometric_denominator_ne ((T * V) ^ 2 * t ^ 2) hE
    rw [i2RegionTerm_row4, i2DepthMass_row4, hqeq]
    unfold Algebra.regionTerm29
    try simp only [inv_inv, pow_one]
    field_simp
    <;> ring
end FourierJacobi.Analysis
