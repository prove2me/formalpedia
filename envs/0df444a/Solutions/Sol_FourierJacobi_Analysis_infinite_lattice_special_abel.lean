-- Prove2me | solution 1 for FourierJacobi.Analysis.infinite_lattice_special_abel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:46.581419+00:00
-- url     : https://prove2.me/submissions/a19b227f-fb85-4ed3-a0de-3d03df6c065f

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_lattice_damped
import Theorems.Thm_FourierJacobi_Analysis_corrected_special_lattice_comparison
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_dampedRational_one
import Theorems.Thm_FourierJacobi_Analysis_hasSum_weightedLatticeTerm_of_norm
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
import Theorems.Thm_FourierJacobi_Analysis_paper_denominator_special_ne_zero
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
theorem _root_.solution (q : ℝ) (a b ε : ℂ) (hq : 2 < q)
    (hε : ε = 1 ∨ ε = -1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε) :
    (∀ T ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
        ‖weightedLatticeTerm q a b (ε * (inverseSqrt q : ℂ)) T p‖) ∧
      HasSum (weightedLatticeTerm q a b (ε * (inverseSqrt q : ℂ)) T)
        (latticeCore q a b (ε * (inverseSqrt q : ℂ)) T)) ∧
    paperC q * paperD1 q a b (ε * (inverseSqrt q : ℂ)) *
      paperD2 q a b (ε * (inverseSqrt q : ℂ)) ≠ 0 ∧
    Tendsto (fun T => ((1 - ε) / ((q : ℂ) + 1)) *
      latticeCore q a b (ε * (inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - ε) / ((q : ℂ) + 1)) *
        paperE q a b (ε * (inverseSqrt q : ℂ)))) := by
  have hq' : 1 < q := by linarith
  refine ⟨?_, paper_denominator_special_ne_zero q hq' a b ε ha hb hε haε hbε,
    corrected_special_lattice_comparison q a b ε hq hε ha hb ha₁ hb₁ hab hab₁ haε hbε⟩
  intro T hT
  have hnε : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hnd : ‖ε * (inverseSqrt q : ℂ)‖ = inverseSqrt q := by
    simp [hnε, abs_of_pos (inverseSqrt_pos hq')]
  have hn := summable_norm_lattice_damped q T a b (ε * (inverseSqrt q : ℂ))
    hq ha hb hT.1 hT.2 (by rw [hnd]) (by rw [hnd]; exact (inverseSqrt_lt_one hq').le)
  exact ⟨hn, hasSum_weightedLatticeTerm_of_norm q T a b (ε * (inverseSqrt q : ℂ)) hn⟩
end FourierJacobi.Analysis
