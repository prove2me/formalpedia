-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i2_depthWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:25:44.506337+00:00
-- url     : https://prove2.me/submissions/dd8f6b6f-cb65-44f3-84a0-e2f1a453080e

import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I2Assembly
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_probability_ge_two
import Theorems.Thm_FourierJacobi_Analysis_hasSum_collisionWeight
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i2Case10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row0
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row1
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row10
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row11
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row12
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row13
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row14
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row15
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row16
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row17
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row18
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row19
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row2
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row20
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row21
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row22
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row23
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row24
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row3
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row4
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row5
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row6
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row7
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row8
import Theorems.Thm_FourierJacobi_Analysis_i2DepthAt_row9
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row0
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row1
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row10
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row11
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row12
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row13
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row14
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row15
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row16
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row17
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row18
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row19
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row2
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row20
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row21
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row22
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row23
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row24
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row3
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row4
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row5
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row6
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row7
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row8
import Theorems.Thm_FourierJacobi_Analysis_i2DepthMass_row9
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row0
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row1
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row10
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row11
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row12
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row13
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row14
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row15
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row16
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row17
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row18
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row19
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row2
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row20
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row21
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row22
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row23
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row24
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row3
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row4
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row5
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row6
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row7
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row8
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row9
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row0
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row1
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row10
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row11
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row12
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row13
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row14
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row15
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row16
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row17
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row18
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row19
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row2
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row20
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row21
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row22
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row23
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row24
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row3
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row4
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row5
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row6
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row7
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row8
import Theorems.Thm_FourierJacobi_Analysis_i2RegionTerm_row9
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row0
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row1
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row10
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row11
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row12
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row13
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row14
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row15
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row16
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row17
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row18
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row19
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row2
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row20
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row21
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row22
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row23
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row24
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row3
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row4
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row5
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row6
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row7
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row8
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row9
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i2Case10Equiv_val
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row0
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row1
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row10
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row11
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row12
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row13
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row14
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row15
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row16
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row17
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row18
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row19
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row2
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row20
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row21
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row22
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row23
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row24
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row3
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row4
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row5
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row6
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row7
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row8
attribute [local simp] FourierJacobi.Analysis.i2DepthAt_row9
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row0
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row1
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row10
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row11
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row12
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row13
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row14
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row15
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row16
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row17
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row18
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row19
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row2
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row20
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row21
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row22
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row23
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row24
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row3
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row4
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row5
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row6
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row7
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row8
attribute [local simp] FourierJacobi.Analysis.i2DepthMass_row9
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row0
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row1
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row10
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row11
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row12
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row13
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row14
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row15
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row16
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row17
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row18
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row19
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row2
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row20
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row21
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row22
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row23
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row24
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row3
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row4
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row5
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row6
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row7
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row8
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row9
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row0
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row1
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row10
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row11
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row12
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row13
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row14
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row15
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row16
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row17
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row18
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row19
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row2
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row20
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row21
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row22
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row23
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row24
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row3
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row4
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row5
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row6
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row7
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row8
attribute [local simp] FourierJacobi.Analysis.i2RegionTerm_row9
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row0
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row1
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row10
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row11
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row12
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row13
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row14
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row15
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row16
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row17
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row18
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row19
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row2
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row20
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row21
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row22
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row23
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row24
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row3
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row4
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row5
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row6
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row7
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row8
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row9
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (ν : Fin 25) (p : I2SpatialRow ν)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    HasSum (i2DepthWeight q ν p) (i2DepthMass q ν) := by
  classical
  fin_cases ν
  · change HasSum (fun c : ℕ => i2DepthWeight q 0 p c) (i2DepthMass q 0)
    simpa only [i2DepthWeight, i2DepthPredicate_row0, if_true, i2DepthMass_row0]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 1 p c) (i2DepthMass q 1)
    simpa only [i2DepthWeight, i2DepthPredicate_row1, if_true, i2DepthMass_row1]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 2 p c) (i2DepthMass q 2)
    simpa only [i2DepthWeight, i2DepthPredicate_row2, if_true, i2DepthMass_row2]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 3 p c) (i2DepthMass q 3)
    simpa only [i2DepthWeight, i2DepthPredicate_row3, if_true, i2DepthMass_row3]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 4 p c) (i2DepthMass q 4)
    have hp := p.property
    change i2SpatialPredicate 4 p.val at hp
    simp only [i2SpatialPredicate_row4] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row4, hw, i2DepthMass_row4]
    convert hasSum_ite_eq (α := ℂ) (β := ℕ) 0 ((q - 2) / (q - 1)) using 1
    funext c
    split_ifs with hc
    · subst c
      simp [collisionProbability]
    · rfl
  · change HasSum (fun c : ℕ => i2DepthWeight q 5 p c) (i2DepthMass q 5)
    have hp := p.property
    change i2SpatialPredicate 5 p.val at hp
    simp only [i2SpatialPredicate_row5] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row5, hw, i2DepthMass_row5]
    convert hasSum_ite_eq (α := ℂ) (β := ℕ) 1 (q⁻¹) using 1
    funext c
    split_ifs with hc
    · subst c
      simp [collisionProbability]
    · rfl
  · change HasSum (fun c : ℕ => i2DepthWeight q 6 p c) (i2DepthMass q 6)
    have hp := p.property
    change i2SpatialPredicate 6 p.val at hp
    simp only [i2SpatialPredicate_row6] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row6, hw, i2DepthMass_row6]
    exact hasSum_i2_probability_ge_two q hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 7 p c) (i2DepthMass q 7)
    simpa only [i2DepthWeight, i2DepthPredicate_row7, if_true, i2DepthMass_row7]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 8 p c) (i2DepthMass q 8)
    simpa only [i2DepthWeight, i2DepthPredicate_row8, if_true, i2DepthMass_row8]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 9 p c) (i2DepthMass q 9)
    simpa only [i2DepthWeight, i2DepthPredicate_row9, if_true, i2DepthMass_row9]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 10 p c) (i2DepthMass q 10)
    simpa only [i2DepthWeight, i2DepthPredicate_row10, if_true, i2DepthMass_row10]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 11 p c) (i2DepthMass q 11)
    simpa only [i2DepthWeight, i2DepthPredicate_row11, if_true, i2DepthMass_row11]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 12 p c) (i2DepthMass q 12)
    simpa only [i2DepthWeight, i2DepthPredicate_row12, if_true, i2DepthMass_row12]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 13 p c) (i2DepthMass q 13)
    simpa only [i2DepthWeight, i2DepthPredicate_row13, if_true, i2DepthMass_row13]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 14 p c) (i2DepthMass q 14)
    simpa only [i2DepthWeight, i2DepthPredicate_row14, if_true, i2DepthMass_row14]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 15 p c) (i2DepthMass q 15)
    simpa only [i2DepthWeight, i2DepthPredicate_row15, if_true, i2DepthMass_row15]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 16 p c) (i2DepthMass q 16)
    simpa only [i2DepthWeight, i2DepthPredicate_row16, if_true, i2DepthMass_row16]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 17 p c) (i2DepthMass q 17)
    simpa only [i2DepthWeight, i2DepthPredicate_row17, if_true, i2DepthMass_row17]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 18 p c) (i2DepthMass q 18)
    simpa only [i2DepthWeight, i2DepthPredicate_row18, if_true, i2DepthMass_row18]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 19 p c) (i2DepthMass q 19)
    simpa only [i2DepthWeight, i2DepthPredicate_row19, if_true, i2DepthMass_row19]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 20 p c) (i2DepthMass q 20)
    have hp := p.property
    change i2SpatialPredicate 20 p.val at hp
    simp only [i2SpatialPredicate_row20] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row20, hw, i2DepthMass_row20]
    convert hasSum_ite_eq (α := ℂ) (β := ℕ) 0 ((q - 2) / (q - 1)) using 1
    funext c
    split_ifs with hc
    · subst c
      simp [collisionProbability]
    · rfl
  · change HasSum (fun c : ℕ => i2DepthWeight q 21 p c) (i2DepthMass q 21)
    have hp := p.property
    change i2SpatialPredicate 21 p.val at hp
    simp only [i2SpatialPredicate_row21] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row21, hw, i2DepthMass_row21]
    convert hasSum_ite_eq (α := ℂ) (β := ℕ) 1 (q⁻¹) using 1
    funext c
    split_ifs with hc
    · subst c
      simp [collisionProbability]
    · rfl
  · change HasSum (fun c : ℕ => i2DepthWeight q 22 p c) (i2DepthMass q 22)
    have hp := p.property
    change i2SpatialPredicate 22 p.val at hp
    simp only [i2SpatialPredicate_row22] at hp
    have he : 2 * p.val.2.2 = p.val.2.1 - 2 := by omega
    have hw (c : ℕ) : collisionWeight q 2 p.val.2.1 p.val.2.2 c = collisionProbability q c := by
      simp [collisionWeight, he]
    simp only [i2DepthWeight, i2DepthPredicate_row22, hw, i2DepthMass_row22]
    exact hasSum_i2_probability_ge_two q hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 23 p c) (i2DepthMass q 23)
    simpa only [i2DepthWeight, i2DepthPredicate_row23, if_true, i2DepthMass_row23]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
  · change HasSum (fun c : ℕ => i2DepthWeight q 24 p c) (i2DepthMass q 24)
    simpa only [i2DepthWeight, i2DepthPredicate_row24, if_true, i2DepthMass_row24]
      using hasSum_collisionWeight q 2 p.val.2.1 p.val.2.2 hq₀ hq₁ hq
end FourierJacobi.Analysis
