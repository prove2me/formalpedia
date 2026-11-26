-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_weightedLatticeTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:16:33.294039+00:00
-- url     : https://prove2.me/submissions/fc958dc1-9e56-458f-b90b-734bd21d314d

import Definitions.Def_FourierJacobi_Analysis_I0Master
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I2Master
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_central_master
import Theorems.Thm_FourierJacobi_Analysis_natural_master_parameters
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Algebra_weylU_unitary
import Theorems.Thm_FourierJacobi_Algebra_weylV_unitary
import Theorems.Thm_FourierJacobi_Analysis_dampedRational_one
import Theorems.Thm_FourierJacobi_Analysis_geometricRange_of_bounds
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10DepthEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10Equiv_val
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
attribute [local simp] FourierJacobi.Analysis.dampedRational_one
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10DepthEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10Equiv_val
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
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex => ‖weightedLatticeTerm q a b d T p‖) := by
  obtain ⟨ht, hq0, hq1, hq2, hqt⟩ := natural_master_parameters hq
  have hq' : 1 < q := by linarith
  have hd : d ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (inverseSqrt_pos hq') hd₀)
  apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro i
  apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro r
  have hg := geometricRange_of_bounds (inverseSqrt_pos hq') (inverseSqrt_lt_one hq')
    hT₀ hT₁ hd₀ hd₁ hstrict (weylU_unitary ha hb i) (weylV_unitary ha hb i)
  have hs := summable_norm_central_master (q : ℂ) (inverseSqrt q : ℂ) d
    (weylU a b i) (weylV a b i) (T : ℂ) ht hd hq0 hq1 hq2 hqt hg r
  simpa only [weightedLatticeTerm, norm_mul] using
    hs.mul_left ‖weylWeights (inverseSqrt q : ℂ) a b i / paperC q‖
end FourierJacobi.Analysis
