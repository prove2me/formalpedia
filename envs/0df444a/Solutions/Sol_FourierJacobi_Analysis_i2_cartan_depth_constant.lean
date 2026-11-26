-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_cartan_depth_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:19.236844+00:00
-- url     : https://prove2.me/submissions/cd204173-a5b2-4cc9-bf63-ba2b934622d5

import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I2Assembly
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i2Case10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_i2Case10_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case1a_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case1b_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case2_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case3a_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case3b_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case3c_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case3d_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case4_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case5_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case6a_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case6aa_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case6aaa_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case6b_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case6bb_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case6bbb_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case6c_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case6cc_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case6ccc_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case7_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case8a_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case8b_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case8c_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case8d_cartan
import Theorems.Thm_FourierJacobi_Analysis_i2Case9_cartan
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
theorem _root_.solution (ν : Fin 25) (p : I2SpatialRow ν) (c : ℕ)
    (hc : i2DepthPredicate ν c) :
    cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c =
      cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt ν) := by
  fin_cases ν
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 0)
    change i2DepthPredicate 0 c at hc
    rw [i2Case1a_cartan p c, i2Case1a_cartan p (i2DepthAt 0)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 1)
    change i2DepthPredicate 1 c at hc
    rw [i2Case1b_cartan p c, i2Case1b_cartan p (i2DepthAt 1)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 2)
    change i2DepthPredicate 2 c at hc
    rw [i2Case2_cartan p c, i2Case2_cartan p (i2DepthAt 2)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 3)
    change i2DepthPredicate 3 c at hc
    rw [i2Case3a_cartan p c, i2Case3a_cartan p (i2DepthAt 3)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 4)
    change i2DepthPredicate 4 c at hc
    rw [i2Case3b_cartan p c (by simpa using hc), i2Case3b_cartan p (i2DepthAt 4) (by rw [i2DepthAt_row4])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 5)
    change i2DepthPredicate 5 c at hc
    rw [i2Case3c_cartan p c (by simpa using hc), i2Case3c_cartan p (i2DepthAt 5) (by rw [i2DepthAt_row5])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 6)
    change i2DepthPredicate 6 c at hc
    rw [i2Case3d_cartan p c (by simpa using hc), i2Case3d_cartan p (i2DepthAt 6) (by rw [i2DepthAt_row6])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 7)
    change i2DepthPredicate 7 c at hc
    rw [i2Case4_cartan p c, i2Case4_cartan p (i2DepthAt 7)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 8)
    change i2DepthPredicate 8 c at hc
    rw [i2Case5_cartan p c, i2Case5_cartan p (i2DepthAt 8)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 9)
    change i2DepthPredicate 9 c at hc
    rw [i2Case6a_cartan p c, i2Case6a_cartan p (i2DepthAt 9)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 10)
    change i2DepthPredicate 10 c at hc
    rw [i2Case6aa_cartan p c, i2Case6aa_cartan p (i2DepthAt 10)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 11)
    change i2DepthPredicate 11 c at hc
    rw [i2Case6aaa_cartan p c, i2Case6aaa_cartan p (i2DepthAt 11)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 12)
    change i2DepthPredicate 12 c at hc
    rw [i2Case6b_cartan p c, i2Case6b_cartan p (i2DepthAt 12)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 13)
    change i2DepthPredicate 13 c at hc
    rw [i2Case6bb_cartan p c, i2Case6bb_cartan p (i2DepthAt 13)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 14)
    change i2DepthPredicate 14 c at hc
    rw [i2Case6bbb_cartan p c, i2Case6bbb_cartan p (i2DepthAt 14)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 15)
    change i2DepthPredicate 15 c at hc
    rw [i2Case6c_cartan p c, i2Case6c_cartan p (i2DepthAt 15)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 16)
    change i2DepthPredicate 16 c at hc
    rw [i2Case6cc_cartan p c, i2Case6cc_cartan p (i2DepthAt 16)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 17)
    change i2DepthPredicate 17 c at hc
    rw [i2Case6ccc_cartan p c, i2Case6ccc_cartan p (i2DepthAt 17)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 18)
    change i2DepthPredicate 18 c at hc
    rw [i2Case7_cartan p c, i2Case7_cartan p (i2DepthAt 18)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 19)
    change i2DepthPredicate 19 c at hc
    rw [i2Case8a_cartan p c, i2Case8a_cartan p (i2DepthAt 19)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 20)
    change i2DepthPredicate 20 c at hc
    rw [i2Case8b_cartan p c (by simpa using hc), i2Case8b_cartan p (i2DepthAt 20) (by rw [i2DepthAt_row20])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 21)
    change i2DepthPredicate 21 c at hc
    rw [i2Case8c_cartan p c (by simpa using hc), i2Case8c_cartan p (i2DepthAt 21) (by rw [i2DepthAt_row21])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 22)
    change i2DepthPredicate 22 c at hc
    rw [i2Case8d_cartan p c (by simpa using hc), i2Case8d_cartan p (i2DepthAt 22) (by rw [i2DepthAt_row22])]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 23)
    change i2DepthPredicate 23 c at hc
    rw [i2Case9_cartan p c, i2Case9_cartan p (i2DepthAt 23)]
  · change cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 c = cartanIndices 2 p.val.1 p.val.2.1 p.val.2.2 (i2DepthAt 24)
    change i2DepthPredicate 24 c at hc
    rw [i2Case10_cartan p c, i2Case10_cartan p (i2DepthAt 24)]
end FourierJacobi.Analysis
