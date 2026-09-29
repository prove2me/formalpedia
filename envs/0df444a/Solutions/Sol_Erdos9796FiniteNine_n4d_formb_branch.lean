-- Prove2me | solution 1 for Erdos9796FiniteNine.n4d_formb_branch
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T02:40:04.563449+00:00
-- url     : https://prove2.me/submissions/e7aae940-ff91-4c37-a2d9-a7284461f1ba

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N4dFormBBranchSupport
import Theorems.Thm_Erdos9796FiniteNine_n4e_core

import Definitions.Def_Erdos9796FiniteNine_N8Interface
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_CGN_CGN6
import Definitions.Def_Erdos9796Counting_Cap_Partition
import Definitions.Def_Erdos9796Counting_Cap_PartitionFromMEC
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_CircumscribedMECPacket
import Definitions.Def_Erdos9796Counting_ConvexCyclicOrder_Construct
import Definitions.Def_Erdos9796Counting_Dumitrescu_L6
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Definitions.Def_Erdos9796Counting_MEC_ArcAngle
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_MEC_Boundary
import Definitions.Def_Erdos9796Counting_Moser_Triangle
import Definitions.Def_Erdos9796Counting_Moser_TriangleNonObtuse
import Definitions.Def_Erdos9796Counting_SignedAreaOangle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Lattice
import Theorems.Thm_Problem97_CGN_CGN4g_strictCapBlockData_of_supportCap_oriented
import Theorems.Thm_Problem97_CGN_CGN6b_nonacute_of_minorCapChainCoords
import Theorems.Thm_Problem97_CGN_CGN6norm_minorCapChainModel_of_mecCapPacket
import Theorems.Thm_Problem97_ConvexIndep_not_collinear_of_card_ge_three
import Theorems.Thm_Problem97_ConvexIndep_not_wbtw
import Theorems.Thm_Problem97_Dumitrescu_three_cap_decomposition
import Theorems.Thm_Problem97_MEC_exists_nonobtuse_circumscribed_triple
import Theorems.Thm_Problem97_MEC_no_diameter_under_k4
import Theorems.Thm_Problem97_MEC_not_collinear_of_three_dist_eq
import Theorems.Thm_Problem97_affineSpan_eq_top_of_not_collinear
import Theorems.Thm_Problem97_card_ge_five_of_K4
import Theorems.Thm_Problem97_center_same_side_as_apex_of_nonobtuse
import Theorems.Thm_Problem97_collinear_of_signedArea2_eq_zero
import Theorems.Thm_Problem97_exists_cut_sorted_enumeration_of_convexIndep
import Theorems.Thm_Problem97_inner_chord_eq_two_mul_inner_midpoint
import Theorems.Thm_Problem97_isCcwConvexPolygon_of_cut_sorted_arcAngle
import Theorems.Thm_Problem97_signedArea2_eq_zero_iff_collinear
import Theorems.Thm_Problem97_signedArea2_sign_eq_oangle_sign
import Theorems.Thm_Problem97_signedArea_prod_eq_inner_mul_dist_sq
import Theorems.Thm_Problem97_three_le_card_of_convexIndep_noncoll

/-
Source: mysticflounder/erdos-97-96-formalization, commit
a46894f6078319d3001d06310531df50af0f6bbd, Erdos9796Proof/P97.
Original mathematical proof credited to the upstream contributors.
This is a faithful Lean 4.33.1 compatibility port and source dependency slice.
Private helpers have distinct module prefixes to preserve separate-file scope.
The assembly generator and diagnostic elaborators are not part of this proof.
-/
/- Exact name exports to the genuine public constants; no intermediate values or nominal structures are introduced. -/
namespace Batch3N9
namespace Problem97.CGN
export _root_.Problem97.CGN (BoundaryCapBlock)
end Problem97.CGN
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (cap_image)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (cap_subset_A)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (casesOn)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (ctorIdx)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (hi)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (hlohi)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (hm)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (idx)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (idx_first)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (idx_last)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (idx_range_exact)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (idx_strict)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (lo)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (mk)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock.mk
export _root_.Problem97.CGN.BoundaryCapBlock.mk (inj)
end Problem97.CGN.BoundaryCapBlock.mk
namespace Problem97.CGN.BoundaryCapBlock.mk
export _root_.Problem97.CGN.BoundaryCapBlock.mk (injEq)
end Problem97.CGN.BoundaryCapBlock.mk
namespace Problem97.CGN.BoundaryCapBlock.mk
export _root_.Problem97.CGN.BoundaryCapBlock.mk (noConfusion)
end Problem97.CGN.BoundaryCapBlock.mk
namespace Problem97.CGN.BoundaryCapBlock.mk
export _root_.Problem97.CGN.BoundaryCapBlock.mk (sizeOf_spec)
end Problem97.CGN.BoundaryCapBlock.mk
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (noConfusion)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (noConfusionType)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (phi_image)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (points_eq)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (rec)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN.BoundaryCapBlock
export _root_.Problem97.CGN.BoundaryCapBlock (recOn)
end Problem97.CGN.BoundaryCapBlock
namespace Problem97.CGN
export _root_.Problem97.CGN (CapIndexPairs)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (HasCapWitness)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (MecCapPacket)
end Problem97.CGN
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (casesOn)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (center)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (ctorIdx)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (disk_mem)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (first_on_circle)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (hm)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (last_on_circle)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (mem_A)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (mk)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket.mk
export _root_.Problem97.CGN.MecCapPacket.mk (inj)
end Problem97.CGN.MecCapPacket.mk
namespace Problem97.CGN.MecCapPacket.mk
export _root_.Problem97.CGN.MecCapPacket.mk (injEq)
end Problem97.CGN.MecCapPacket.mk
namespace Problem97.CGN.MecCapPacket.mk
export _root_.Problem97.CGN.MecCapPacket.mk (noConfusion)
end Problem97.CGN.MecCapPacket.mk
namespace Problem97.CGN.MecCapPacket.mk
export _root_.Problem97.CGN.MecCapPacket.mk (sizeOf_spec)
end Problem97.CGN.MecCapPacket.mk
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (noConfusion)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (noConfusionType)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (radius)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (radius_nonneg)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (rec)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN.MecCapPacket
export _root_.Problem97.CGN.MecCapPacket (recOn)
end Problem97.CGN.MecCapPacket
namespace Problem97.CGN
export _root_.Problem97.CGN (MinorCapChainCoords)
end Problem97.CGN
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (X)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (X_first)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (X_last)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (Y)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (Y_first)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (Y_last)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (adjacent_slopes_decreasing)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (casesOn)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (ctorIdx)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (hm)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (mk)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords.mk
export _root_.Problem97.CGN.MinorCapChainCoords.mk (inj)
end Problem97.CGN.MinorCapChainCoords.mk
namespace Problem97.CGN.MinorCapChainCoords.mk
export _root_.Problem97.CGN.MinorCapChainCoords.mk (injEq)
end Problem97.CGN.MinorCapChainCoords.mk
namespace Problem97.CGN.MinorCapChainCoords.mk
export _root_.Problem97.CGN.MinorCapChainCoords.mk (noConfusion)
end Problem97.CGN.MinorCapChainCoords.mk
namespace Problem97.CGN.MinorCapChainCoords.mk
export _root_.Problem97.CGN.MinorCapChainCoords.mk (sizeOf_spec)
end Problem97.CGN.MinorCapChainCoords.mk
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (noConfusion)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (noConfusionType)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (rec)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (recOn)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (unit_disk)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (x_strict)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN.MinorCapChainCoords
export _root_.Problem97.CGN.MinorCapChainCoords (y_nonneg)
end Problem97.CGN.MinorCapChainCoords
namespace Problem97.CGN
export _root_.Problem97.CGN (MinorCapChainModel)
end Problem97.CGN
namespace Problem97.CGN.MinorCapChainModel
export _root_.Problem97.CGN.MinorCapChainModel (casesOn)
end Problem97.CGN.MinorCapChainModel
namespace Problem97.CGN.MinorCapChainModel
export _root_.Problem97.CGN.MinorCapChainModel (coords)
end Problem97.CGN.MinorCapChainModel
namespace Problem97.CGN.MinorCapChainModel
export _root_.Problem97.CGN.MinorCapChainModel (ctorIdx)
end Problem97.CGN.MinorCapChainModel
namespace Problem97.CGN.MinorCapChainModel
export _root_.Problem97.CGN.MinorCapChainModel (mk)
end Problem97.CGN.MinorCapChainModel
namespace Problem97.CGN.MinorCapChainModel.mk
export _root_.Problem97.CGN.MinorCapChainModel.mk (inj)
end Problem97.CGN.MinorCapChainModel.mk
namespace Problem97.CGN.MinorCapChainModel.mk
export _root_.Problem97.CGN.MinorCapChainModel.mk (injEq)
end Problem97.CGN.MinorCapChainModel.mk
namespace Problem97.CGN.MinorCapChainModel.mk
export _root_.Problem97.CGN.MinorCapChainModel.mk (noConfusion)
end Problem97.CGN.MinorCapChainModel.mk
namespace Problem97.CGN.MinorCapChainModel.mk
export _root_.Problem97.CGN.MinorCapChainModel.mk (sizeOf_spec)
end Problem97.CGN.MinorCapChainModel.mk
namespace Problem97.CGN.MinorCapChainModel
export _root_.Problem97.CGN.MinorCapChainModel (noConfusion)
end Problem97.CGN.MinorCapChainModel
namespace Problem97.CGN.MinorCapChainModel
export _root_.Problem97.CGN.MinorCapChainModel (noConfusionType)
end Problem97.CGN.MinorCapChainModel
namespace Problem97.CGN.MinorCapChainModel
export _root_.Problem97.CGN.MinorCapChainModel (points_eq)
end Problem97.CGN.MinorCapChainModel
namespace Problem97.CGN.MinorCapChainModel
export _root_.Problem97.CGN.MinorCapChainModel (rec)
end Problem97.CGN.MinorCapChainModel
namespace Problem97.CGN.MinorCapChainModel
export _root_.Problem97.CGN.MinorCapChainModel (recOn)
end Problem97.CGN.MinorCapChainModel
namespace Problem97.CGN
export _root_.Problem97.CGN (MinorCapSideHypotheses)
end Problem97.CGN
namespace Problem97.CGN.MinorCapSideHypotheses
export _root_.Problem97.CGN.MinorCapSideHypotheses (cap_side_nonneg)
end Problem97.CGN.MinorCapSideHypotheses
namespace Problem97.CGN.MinorCapSideHypotheses
export _root_.Problem97.CGN.MinorCapSideHypotheses (casesOn)
end Problem97.CGN.MinorCapSideHypotheses
namespace Problem97.CGN.MinorCapSideHypotheses
export _root_.Problem97.CGN.MinorCapSideHypotheses (center_side_nonpos)
end Problem97.CGN.MinorCapSideHypotheses
namespace Problem97.CGN.MinorCapSideHypotheses
export _root_.Problem97.CGN.MinorCapSideHypotheses (mk)
end Problem97.CGN.MinorCapSideHypotheses
namespace Problem97.CGN.MinorCapSideHypotheses
export _root_.Problem97.CGN.MinorCapSideHypotheses (rec)
end Problem97.CGN.MinorCapSideHypotheses
namespace Problem97.CGN.MinorCapSideHypotheses
export _root_.Problem97.CGN.MinorCapSideHypotheses (recOn)
end Problem97.CGN.MinorCapSideHypotheses
namespace Problem97.CGN
export _root_.Problem97.CGN (NoCapWitness)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (OrderedCap)
end Problem97.CGN
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (casesOn)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (ctorIdx)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (injective)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (map)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (mk)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN.OrderedCap.mk
export _root_.Problem97.CGN.OrderedCap.mk (inj)
end Problem97.CGN.OrderedCap.mk
namespace Problem97.CGN.OrderedCap.mk
export _root_.Problem97.CGN.OrderedCap.mk (injEq)
end Problem97.CGN.OrderedCap.mk
namespace Problem97.CGN.OrderedCap.mk
export _root_.Problem97.CGN.OrderedCap.mk (noConfusion)
end Problem97.CGN.OrderedCap.mk
namespace Problem97.CGN.OrderedCap.mk
export _root_.Problem97.CGN.OrderedCap.mk (sizeOf_spec)
end Problem97.CGN.OrderedCap.mk
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (noConfusion)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (noConfusionType)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (points)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (rec)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN.OrderedCap
export _root_.Problem97.CGN.OrderedCap (recOn)
end Problem97.CGN.OrderedCap
namespace Problem97.CGN
export _root_.Problem97.CGN (SimilarityTransportData)
end Problem97.CGN
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (casesOn)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (convexHull_mem_iff)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (ctorIdx)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (dist_eq_iff)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (dist_image)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (halfplane_sign)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (mk)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData.mk
export _root_.Problem97.CGN.SimilarityTransportData.mk (inj)
end Problem97.CGN.SimilarityTransportData.mk
namespace Problem97.CGN.SimilarityTransportData.mk
export _root_.Problem97.CGN.SimilarityTransportData.mk (injEq)
end Problem97.CGN.SimilarityTransportData.mk
namespace Problem97.CGN.SimilarityTransportData.mk
export _root_.Problem97.CGN.SimilarityTransportData.mk (noConfusion)
end Problem97.CGN.SimilarityTransportData.mk
namespace Problem97.CGN.SimilarityTransportData.mk
export _root_.Problem97.CGN.SimilarityTransportData.mk (sizeOf_spec)
end Problem97.CGN.SimilarityTransportData.mk
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (noConfusion)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (noConfusionType)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (orientation)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (orientation_sq)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (rec)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (recOn)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (scale)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN.SimilarityTransportData
export _root_.Problem97.CGN.SimilarityTransportData (scale_pos)
end Problem97.CGN.SimilarityTransportData
namespace Problem97.CGN
export _root_.Problem97.CGN (StrictCapBlockData)
end Problem97.CGN
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (Block)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (Hord)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (Hside)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (L)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (Packet)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (casesOn)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (ctorIdx)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (m)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (mk)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData.mk
export _root_.Problem97.CGN.StrictCapBlockData.mk (inj)
end Problem97.CGN.StrictCapBlockData.mk
namespace Problem97.CGN.StrictCapBlockData.mk
export _root_.Problem97.CGN.StrictCapBlockData.mk (injEq)
end Problem97.CGN.StrictCapBlockData.mk
namespace Problem97.CGN.StrictCapBlockData.mk
export _root_.Problem97.CGN.StrictCapBlockData.mk (noConfusion)
end Problem97.CGN.StrictCapBlockData.mk
namespace Problem97.CGN.StrictCapBlockData.mk
export _root_.Problem97.CGN.StrictCapBlockData.mk (sizeOf_spec)
end Problem97.CGN.StrictCapBlockData.mk
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (n)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (noConfusion)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (noConfusionType)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (phi)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (phi_ccw)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (phi_injective)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (rec)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN.StrictCapBlockData
export _root_.Problem97.CGN.StrictCapBlockData (recOn)
end Problem97.CGN.StrictCapBlockData
namespace Problem97.CGN
export _root_.Problem97.CGN (StrictCapOrder)
end Problem97.CGN
namespace Problem97.CGN.StrictCapOrder
export _root_.Problem97.CGN.StrictCapOrder (casesOn)
end Problem97.CGN.StrictCapOrder
namespace Problem97.CGN.StrictCapOrder
export _root_.Problem97.CGN.StrictCapOrder (chord_projection_strict)
end Problem97.CGN.StrictCapOrder
namespace Problem97.CGN.StrictCapOrder
export _root_.Problem97.CGN.StrictCapOrder (consecutive_turn_nonpos)
end Problem97.CGN.StrictCapOrder
namespace Problem97.CGN.StrictCapOrder
export _root_.Problem97.CGN.StrictCapOrder (hm)
end Problem97.CGN.StrictCapOrder
namespace Problem97.CGN.StrictCapOrder
export _root_.Problem97.CGN.StrictCapOrder (mk)
end Problem97.CGN.StrictCapOrder
namespace Problem97.CGN.StrictCapOrder
export _root_.Problem97.CGN.StrictCapOrder (rec)
end Problem97.CGN.StrictCapOrder
namespace Problem97.CGN.StrictCapOrder
export _root_.Problem97.CGN.StrictCapOrder (recOn)
end Problem97.CGN.StrictCapOrder
namespace Problem97.CGN.StrictCapOrder
export _root_.Problem97.CGN.StrictCapOrder (subchord_open_side_iff_A)
end Problem97.CGN.StrictCapOrder
namespace Problem97.CGN
export _root_.Problem97.CGN (WitnessedPairsAt)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (WitnessesCapEdgeAt)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (adjSlopeNat)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (adjacentSlope)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (chordFrame)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (edgeAt)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (finIndex)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (firstIndex)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (lastIndex)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (nextAdjacentSlope)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (point)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (slopeAt)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (vec2)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (xCoord)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (yCoord)
end Problem97.CGN
namespace Problem97
export _root_.Problem97 (CapPartition)
end Problem97
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (C1)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (C1_sub)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (C2)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (C2_sub)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (C3)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (C3_sub)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (M_card)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (M_sub)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (casesOn)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (ctorIdx)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (mk)
end Problem97.CapPartition
namespace Problem97.CapPartition.mk
export _root_.Problem97.CapPartition.mk (inj)
end Problem97.CapPartition.mk
namespace Problem97.CapPartition.mk
export _root_.Problem97.CapPartition.mk (injEq)
end Problem97.CapPartition.mk
namespace Problem97.CapPartition.mk
export _root_.Problem97.CapPartition.mk (noConfusion)
end Problem97.CapPartition.mk
namespace Problem97.CapPartition.mk
export _root_.Problem97.CapPartition.mk (sizeOf_spec)
end Problem97.CapPartition.mk
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (moser_in_two)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (noConfusion)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (noConfusionType)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (nonmoser_in_one)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (rec)
end Problem97.CapPartition
namespace Problem97.CapPartition
export _root_.Problem97.CapPartition (recOn)
end Problem97.CapPartition
namespace Problem97
export _root_.Problem97 (CapTriple)
end Problem97
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (C1)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (C1_subset)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (C2)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (C2_subset)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (C3)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (C3_subset)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (arc_membership)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (casesOn)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (ctorIdx)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (mk)
end Problem97.CapTriple
namespace Problem97.CapTriple.mk
export _root_.Problem97.CapTriple.mk (inj)
end Problem97.CapTriple.mk
namespace Problem97.CapTriple.mk
export _root_.Problem97.CapTriple.mk (injEq)
end Problem97.CapTriple.mk
namespace Problem97.CapTriple.mk
export _root_.Problem97.CapTriple.mk (noConfusion)
end Problem97.CapTriple.mk
namespace Problem97.CapTriple.mk
export _root_.Problem97.CapTriple.mk (sizeOf_spec)
end Problem97.CapTriple.mk
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (moser_in_two)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (noConfusion)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (noConfusionType)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (nonmoser_in_one)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (rec)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (recOn)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (toCapPartition)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (v1_mem_C2)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (v1_mem_C3)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (v1_notin_C1)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (v2_mem_C1)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (v2_mem_C3)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (v2_notin_C2)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (v3_mem_C1)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (v3_mem_C2)
end Problem97.CapTriple
namespace Problem97.CapTriple
export _root_.Problem97.CapTriple (v3_notin_C3)
end Problem97.CapTriple
namespace Problem97
export _root_.Problem97 (CircumscribedMECPacket)
end Problem97
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (casesOn)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (center)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (ctorIdx)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (disk_contains_A)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (inner_at_v1)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (inner_at_v2)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (inner_at_v3)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (mk)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket.mk
export _root_.Problem97.CircumscribedMECPacket.mk (inj)
end Problem97.CircumscribedMECPacket.mk
namespace Problem97.CircumscribedMECPacket.mk
export _root_.Problem97.CircumscribedMECPacket.mk (injEq)
end Problem97.CircumscribedMECPacket.mk
namespace Problem97.CircumscribedMECPacket.mk
export _root_.Problem97.CircumscribedMECPacket.mk (noConfusion)
end Problem97.CircumscribedMECPacket.mk
namespace Problem97.CircumscribedMECPacket.mk
export _root_.Problem97.CircumscribedMECPacket.mk (sizeOf_spec)
end Problem97.CircumscribedMECPacket.mk
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (moser_on_boundary_1)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (moser_on_boundary_2)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (moser_on_boundary_3)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (noConfusion)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (noConfusionType)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (ofNonObtuse)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (radius)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (radius_pos)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (rec)
end Problem97.CircumscribedMECPacket
namespace Problem97.CircumscribedMECPacket
export _root_.Problem97.CircumscribedMECPacket (recOn)
end Problem97.CircumscribedMECPacket
namespace Problem97
export _root_.Problem97 (ConvexIndep)
end Problem97
namespace Problem97.Dumitrescu
export _root_.Problem97.Dumitrescu (capPairApexes)
end Problem97.Dumitrescu
namespace Problem97
export _root_.Problem97 (IsoscelesPairsAt)
end Problem97
namespace Problem97.MEC
export _root_.Problem97.MEC (MoserTriangle)
end Problem97.MEC
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (case_split)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (casesOn)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (ctorIdx)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (mk)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle.mk
export _root_.Problem97.MEC.MoserTriangle.mk (inj)
end Problem97.MEC.MoserTriangle.mk
namespace Problem97.MEC.MoserTriangle.mk
export _root_.Problem97.MEC.MoserTriangle.mk (injEq)
end Problem97.MEC.MoserTriangle.mk
namespace Problem97.MEC.MoserTriangle.mk
export _root_.Problem97.MEC.MoserTriangle.mk (noConfusion)
end Problem97.MEC.MoserTriangle.mk
namespace Problem97.MEC.MoserTriangle.mk
export _root_.Problem97.MEC.MoserTriangle.mk (sizeOf_spec)
end Problem97.MEC.MoserTriangle.mk
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (noConfusion)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (noConfusionType)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (rec)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (recOn)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (toStructural)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (v1)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (v1_boundary)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (v1_mem)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (v2)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (v2_boundary)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (v2_mem)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (v3)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (v3_boundary)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC.MoserTriangle
export _root_.Problem97.MEC.MoserTriangle (v3_mem)
end Problem97.MEC.MoserTriangle
namespace Problem97.MEC
export _root_.Problem97.MEC (NonObtuseCircumscribedMoserTriangle)
end Problem97.MEC
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (casesOn)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (ctorIdx)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (inner_at_v1)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (inner_at_v2)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (inner_at_v3)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (mk)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk (inj)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk (injEq)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk (noConfusion)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk (sizeOf_spec)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle.mk
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (noConfusion)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (noConfusionType)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (rec)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (recOn)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC.NonObtuseCircumscribedMoserTriangle
export _root_.Problem97.MEC.NonObtuseCircumscribedMoserTriangle (toMoserTriangle)
end Problem97.MEC.NonObtuseCircumscribedMoserTriangle
namespace Problem97.MEC
export _root_.Problem97.MEC (boundary)
end Problem97.MEC
namespace Problem97.MEC
export _root_.Problem97.MEC (mec)
end Problem97.MEC
namespace Problem97.MEC
export _root_.Problem97.MEC (mec_radius_pos)
end Problem97.MEC
namespace Problem97
export _root_.Problem97 (MinEnclosingCircle)
end Problem97
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (casesOn)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (center)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (ctorIdx)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (enclosing)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (exists_mec)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (minimal)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (mk)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle.mk
export _root_.Problem97.MinEnclosingCircle.mk (inj)
end Problem97.MinEnclosingCircle.mk
namespace Problem97.MinEnclosingCircle.mk
export _root_.Problem97.MinEnclosingCircle.mk (injEq)
end Problem97.MinEnclosingCircle.mk
namespace Problem97.MinEnclosingCircle.mk
export _root_.Problem97.MinEnclosingCircle.mk (noConfusion)
end Problem97.MinEnclosingCircle.mk
namespace Problem97.MinEnclosingCircle.mk
export _root_.Problem97.MinEnclosingCircle.mk (sizeOf_spec)
end Problem97.MinEnclosingCircle.mk
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (noConfusion)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (noConfusionType)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (radius)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (radius_nn)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (rec)
end Problem97.MinEnclosingCircle
namespace Problem97.MinEnclosingCircle
export _root_.Problem97.MinEnclosingCircle (recOn)
end Problem97.MinEnclosingCircle
namespace Problem97
export _root_.Problem97 (MoserTriangle)
end Problem97
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (casesOn)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (ctorIdx)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (mk)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle.mk
export _root_.Problem97.MoserTriangle.mk (inj)
end Problem97.MoserTriangle.mk
namespace Problem97.MoserTriangle.mk
export _root_.Problem97.MoserTriangle.mk (injEq)
end Problem97.MoserTriangle.mk
namespace Problem97.MoserTriangle.mk
export _root_.Problem97.MoserTriangle.mk (noConfusion)
end Problem97.MoserTriangle.mk
namespace Problem97.MoserTriangle.mk
export _root_.Problem97.MoserTriangle.mk (sizeOf_spec)
end Problem97.MoserTriangle.mk
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (noConfusion)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (noConfusionType)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (rec)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (recOn)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (v1)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (v12_ne)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (v13_ne)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (v1_mem)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (v2)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (v23_ne)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (v2_mem)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (v3)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (v3_mem)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (verts)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (verts_card)
end Problem97.MoserTriangle
namespace Problem97.MoserTriangle
export _root_.Problem97.MoserTriangle (verts_subset)
end Problem97.MoserTriangle
namespace Problem97
export _root_.Problem97 (OnArcOpposite)
end Problem97
namespace Problem97
export _root_.Problem97 (SurplusCapPacket)
end Problem97
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (casesOn)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (ctorIdx)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (hA)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (hCirc)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (hncol)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (match_1)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (mk)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket.mk
export _root_.Problem97.SurplusCapPacket.mk (inj)
end Problem97.SurplusCapPacket.mk
namespace Problem97.SurplusCapPacket.mk
export _root_.Problem97.SurplusCapPacket.mk (injEq)
end Problem97.SurplusCapPacket.mk
namespace Problem97.SurplusCapPacket.mk
export _root_.Problem97.SurplusCapPacket.mk (noConfusion)
end Problem97.SurplusCapPacket.mk
namespace Problem97.SurplusCapPacket.mk
export _root_.Problem97.SurplusCapPacket.mk (sizeOf_spec)
end Problem97.SurplusCapPacket.mk
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (noConfusion)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (noConfusionType)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (partition)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (rec)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (recOn)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (surplus)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (surplusIdx)
end Problem97.SurplusCapPacket
namespace Problem97.SurplusCapPacket
export _root_.Problem97.SurplusCapPacket (triangleNonObtuse)
end Problem97.SurplusCapPacket
namespace Problem97
export _root_.Problem97 (arcAngle)
end Problem97
namespace Problem97
export _root_.Problem97 (cutKey)
end Problem97
namespace Problem97
export _root_.Problem97 (iCount)
end Problem97
namespace Problem97
export _root_.Problem97 (iCountAt)
end Problem97
namespace Problem97
export _root_.Problem97 (signedArea2)
end Problem97
namespace Problem97
export _root_.Problem97 (stdOrientation)
end Problem97
namespace Problem97.CGN
export _root_.Problem97.CGN (CGN4g_strictCapBlockData_of_supportCap_oriented)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (CGN6b_nonacute_of_minorCapChainCoords)
end Problem97.CGN
namespace Problem97.CGN
export _root_.Problem97.CGN (CGN6norm_minorCapChainModel_of_mecCapPacket)
end Problem97.CGN
namespace Problem97.ConvexIndep
export _root_.Problem97.ConvexIndep (not_collinear_of_card_ge_three)
end Problem97.ConvexIndep
namespace Problem97.ConvexIndep
export _root_.Problem97.ConvexIndep (not_wbtw)
end Problem97.ConvexIndep
namespace Problem97.Dumitrescu
export _root_.Problem97.Dumitrescu (three_cap_decomposition)
end Problem97.Dumitrescu
namespace Problem97.MEC
export _root_.Problem97.MEC (exists_nonobtuse_circumscribed_triple)
end Problem97.MEC
namespace Problem97.MEC
export _root_.Problem97.MEC (no_diameter_under_k4)
end Problem97.MEC
namespace Problem97.MEC
export _root_.Problem97.MEC (not_collinear_of_three_dist_eq)
end Problem97.MEC
namespace Problem97
export _root_.Problem97 (affineSpan_eq_top_of_not_collinear)
end Problem97
namespace Problem97
export _root_.Problem97 (card_ge_five_of_K4)
end Problem97
namespace Problem97
export _root_.Problem97 (center_same_side_as_apex_of_nonobtuse)
end Problem97
namespace Problem97
export _root_.Problem97 (collinear_of_signedArea2_eq_zero)
end Problem97
namespace Problem97
export _root_.Problem97 (exists_cut_sorted_enumeration_of_convexIndep)
end Problem97
namespace Problem97
export _root_.Problem97 (inner_chord_eq_two_mul_inner_midpoint)
end Problem97
namespace Problem97
export _root_.Problem97 (isCcwConvexPolygon_of_cut_sorted_arcAngle)
end Problem97
namespace Problem97
export _root_.Problem97 (signedArea2_eq_zero_iff_collinear)
end Problem97
namespace Problem97
export _root_.Problem97 (signedArea2_sign_eq_oangle_sign)
end Problem97
namespace Problem97
export _root_.Problem97 (signedArea_prod_eq_inner_mul_dist_sq)
end Problem97
namespace Problem97
export _root_.Problem97 (three_le_card_of_convexIndep_noncoll)
end Problem97
end Batch3N9


open scoped EuclideanGeometry InnerProductSpace

-- Original module: Solutions.Batch3N9.Foundation
section Batch3N9Unit000
namespace Batch3N9
open scoped EuclideanGeometry
namespace Problem97
export Erdos97 (HasNEquidistantPointsAt HasNEquidistantPointsOn)
theorem dist_sq_coord (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
abbrev FiniteN9ClosureStatement : Prop :=
  ∀ A : Finset ℝ², A.card = 9 → ConvexIndep A →
    ¬ HasNEquidistantProperty 4 A
end Problem97
end Batch3N9
end Batch3N9Unit000

-- Original module: Solutions.Batch3N9.IsoscelesCount
section Batch3N9Unit001
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit001

-- Original module: Solutions.Batch3N9.CountingArithmetic
section Batch3N9Unit002
namespace Batch3N9
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit002

-- Original module: Solutions.Batch3N9.ConvexIndepHelpers
section Batch3N9Unit003
namespace Batch3N9
open scoped EuclideanGeometry
namespace Problem97
theorem ConvexIndep.mono {A B : Finset ℝ²} (hBA : B ⊆ A)
    (hA : ConvexIndep A) : ConvexIndep B := by
  intro a haB hmem
  have haA : a ∈ (A : Set ℝ²) := Finset.coe_subset.mpr hBA haB
  have hsub : ((B : Set ℝ²) \ {a}) ⊆ ((A : Set ℝ²) \ {a}) :=
    Set.diff_subset_diff_left (Finset.coe_subset.mpr hBA)
  exact hA a haA (convexHull_mono hsub hmem)
namespace _root_.Problem97.ConvexIndep
export _root_.Batch3N9.Problem97.ConvexIndep (mono)
end _root_.Problem97.ConvexIndep
theorem ConvexIndep.erase {A : Finset ℝ²} (x : ℝ²)
    (hA : ConvexIndep A) : ConvexIndep (A.erase x) :=
  ConvexIndep.mono (Finset.erase_subset x A) hA
namespace _root_.Problem97.ConvexIndep
export _root_.Batch3N9.Problem97.ConvexIndep (erase)
end _root_.Problem97.ConvexIndep
theorem collinear_three_wbtw {x y z : ℝ²}
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) :
    Wbtw ℝ x y z ∨ Wbtw ℝ y z x ∨ Wbtw ℝ z x y := by
  simpa using hcol.wbtw_or_wbtw_or_wbtw
theorem ConvexIndep.not_three_collinear {A : Finset ℝ²}
    (hA : ConvexIndep A) {x y z : ℝ²} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) : False := by
  rcases collinear_three_wbtw hcol with hw | hw | hw
  · exact hA.not_wbtw hx hy hz hw hxy.symm hyz
  · exact hA.not_wbtw hy hz hx hw hyz.symm hxz.symm
  · exact hA.not_wbtw hz hx hy hw hxz hxy
namespace _root_.Problem97.ConvexIndep
export _root_.Batch3N9.Problem97.ConvexIndep (not_three_collinear)
end _root_.Problem97.ConvexIndep
end Problem97
end Batch3N9
end Batch3N9Unit003

-- Original module: Solutions.Batch3N9.MEC.Basic
section Batch3N9Unit004
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace MinEnclosingCircle
end MinEnclosingCircle
namespace MEC
end MEC
end Problem97
end Batch3N9
end Batch3N9Unit004

-- Original module: Solutions.Batch3N9.MEC.Boundary
section Batch3N9Unit005
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace MEC
end MEC
end Problem97
end Batch3N9
end Batch3N9Unit005

-- Original module: Solutions.Batch3N9.Moser.Triangle
section Batch3N9Unit006
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace MEC
end MEC
end Problem97
end Batch3N9
end Batch3N9Unit006

-- Original module: Solutions.Batch3N9.NoDiameterUnderK4
section Batch3N9Unit007
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace MEC
end MEC
end Problem97
end Batch3N9
end Batch3N9Unit007

-- Original module: Solutions.Batch3N9.SmallerCounterexample
section Batch3N9Unit008
namespace Batch3N9
open scoped EuclideanGeometry
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit008

-- Original module: Solutions.Batch3N9.Cap.Partition
section Batch3N9Unit009
namespace Batch3N9
open Finset
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit009

-- Original module: Solutions.Batch3N9.Cap.Structure
section Batch3N9Unit010
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace MoserTriangle
variable {A : Finset ℝ²}
end MoserTriangle
namespace CapTriple
variable {A : Finset ℝ²} {M : MoserTriangle A}
end CapTriple
end Problem97
end Batch3N9
end Batch3N9Unit010

-- Original module: Solutions.Batch3N9.Dumitrescu.L1
section Batch3N9Unit011
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace Dumitrescu
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit011

-- Original module: Solutions.Batch3N9.Dumitrescu.L3
section Batch3N9Unit012
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace Dumitrescu
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit012

-- Original module: Solutions.Batch3N9.Dumitrescu.L5
section Batch3N9Unit013
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace Dumitrescu
noncomputable def capWitnessPairs (A C : Finset ℝ²) : Finset (Finset ℝ²) :=
  (C.powersetCard 2).filter
    (fun xy => ∃ a ∈ A, a ∉ C ∧ ∃ r : ℝ, ∀ q ∈ xy, dist a q = r)
structure CapWitnessRanking (A C : Finset ℝ²) where
  target : Finset ℝ²
  target_subset : target ⊆ C
  target_card_le : target.card ≤ C.card - 1
  rank : Finset ℝ² → ℝ²
  rank_mem : ∀ xy ∈ capWitnessPairs A C, rank xy ∈ target
  rank_injOn : Set.InjOn rank (capWitnessPairs A C : Set (Finset ℝ²))
namespace CapWitnessRanking
variable {A C : Finset ℝ²}
end CapWitnessRanking
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit013

-- Original module: Solutions.Batch3N9.Dumitrescu.L6
section Batch3N9Unit014
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace Dumitrescu
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit014

-- Original module: Solutions.Batch3N9.MidpointInequality
section Batch3N9Unit015
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit015

-- Original module: Solutions.Batch3N9.Cap.ArcInscribedAngle
section Batch3N9Unit016
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit016

-- Original module: Solutions.Batch3N9.CircumcenterSide
section Batch3N9Unit017
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit017

-- Original module: Solutions.Batch3N9.Moser.TriangleNonObtuse
section Batch3N9Unit018
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open Finset
namespace Problem97
namespace MEC
end MEC
end Problem97
end Batch3N9
end Batch3N9Unit018

-- Original module: Solutions.Batch3N9.Cap.PartitionFromMEC
section Batch3N9Unit019
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace MEC
end MEC
namespace SurplusCapPacket
variable {A : Finset ℝ²}
@[reducible] def triangle (S : SurplusCapPacket A) : MoserTriangle A :=
  S.triangleNonObtuse.toMoserTriangle.toStructural S.hCirc
namespace _root_.Problem97.SurplusCapPacket
export _root_.Batch3N9.Problem97.SurplusCapPacket (triangle)
end _root_.Problem97.SurplusCapPacket
end SurplusCapPacket
namespace SurplusCapPacket
@[reducible] def capByIndex
    {A : Finset ℝ²} (S : SurplusCapPacket A) (i : Fin 3) : Finset ℝ² :=
  match i.1 with
  | 0 => S.partition.C1
  | 1 => S.partition.C2
  | _ => S.partition.C3
namespace _root_.Problem97.SurplusCapPacket
export _root_.Batch3N9.Problem97.SurplusCapPacket (capByIndex)
end _root_.Problem97.SurplusCapPacket
@[reducible] noncomputable def capInteriorByIndex
    {A : Finset ℝ²} (S : SurplusCapPacket A) (i : Fin 3) : Finset ℝ² :=
  match i.1 with
  | 0 => (S.partition.C1.erase (_root_.Batch3N9.Problem97.SurplusCapPacket.triangle S).v2).erase (_root_.Batch3N9.Problem97.SurplusCapPacket.triangle S).v3
  | 1 => (S.partition.C2.erase (_root_.Batch3N9.Problem97.SurplusCapPacket.triangle S).v3).erase (_root_.Batch3N9.Problem97.SurplusCapPacket.triangle S).v1
  | _ => (S.partition.C3.erase (_root_.Batch3N9.Problem97.SurplusCapPacket.triangle S).v1).erase (_root_.Batch3N9.Problem97.SurplusCapPacket.triangle S).v2
namespace _root_.Problem97.SurplusCapPacket
export _root_.Batch3N9.Problem97.SurplusCapPacket (capInteriorByIndex)
end _root_.Problem97.SurplusCapPacket
theorem capInteriorByIndex_subset
    {A : Finset ℝ²} (S : SurplusCapPacket A) (i : Fin 3) :
    (_root_.Batch3N9.Problem97.SurplusCapPacket.capInteriorByIndex S) i ⊆ A := by
  intro x hx
  fin_cases i
  · simp only [capInteriorByIndex] at hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    exact S.partition.C1_subset hx.2.2
  · simp only [capInteriorByIndex] at hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    exact S.partition.C2_subset hx.2.2
  · simp only [capInteriorByIndex] at hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    exact S.partition.C3_subset hx.2.2
namespace _root_.Problem97.SurplusCapPacket
export _root_.Batch3N9.Problem97.SurplusCapPacket (capInteriorByIndex_subset)
end _root_.Problem97.SurplusCapPacket
end SurplusCapPacket
end Problem97
end Batch3N9
end Batch3N9Unit019

-- Original module: Solutions.Batch3N9.Cap.ConeContainment
section Batch3N9Unit020
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit020

-- Original module: Solutions.Batch3N9.Cap.ArcInteriorPoints
section Batch3N9Unit021
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
namespace Problem97
theorem inner_midpoint_eq_signedArea_prod_of_chord_sphere
    (v2 v3 v O : ℝ²)
    (heq : ‖v2 - O‖ ^ 2 = ‖v3 - O‖ ^ 2) :
    ⟪midpoint ℝ v2 v3 - v, midpoint ℝ v2 v3 - O⟫_ℝ * ‖v3 - v2‖ ^ 2
      = signedArea2 O v2 v3 * signedArea2 v v2 v3 := by
  have norm_sub_sq : ∀ (x y : ℝ²),
      ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := fun x y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply]
  have inner_eq : ∀ (a b : ℝ²),
      ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 := fun a b => by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two, mul_comm (a _) (b _)]
  have hmid : ∀ i : Fin 2, (midpoint ℝ v2 v3) i = ((v2 i + v3 i) : ℝ) / 2 := by
    intro i; rw [midpoint_eq_smul_add]
    simp [PiLp.smul_apply, PiLp.add_apply, invOf_eq_inv]; ring
  rw [norm_sub_sq v2 O, norm_sub_sq v3 O] at heq
  rw [norm_sub_sq v3 v2, inner_eq]
  simp only [signedArea2, PiLp.sub_apply, hmid]
  set a := v2 0; set b := v2 1; set c := v3 0; set d := v3 1
  set p := v 0; set q := v 1
  linear_combination (1 / 2 : ℝ) *
    (((a + c) / 2 - p) * (a - c) + ((b + d) / 2 - q) * (b - d)) * heq
theorem signedArea_prod_pos_trans {A B C : ℝ}
    (hAC : 0 < A * C) (hBC : 0 < B * C) : 0 < A * B := by
  rcases lt_trichotomy C 0 with hC | hC | hC
  · exact mul_pos_of_neg_of_neg (by nlinarith only [hAC, hC]) (by nlinarith only [hBC, hC])
  · subst hC; simp at hAC
  · exact mul_pos (by nlinarith only [hAC, hC]) (by nlinarith only [hBC, hC])
theorem signedArea_prod_pos_of_inner_midpoint_pos
    {v3 x a O : ℝ²}
    (heq : ‖v3 - O‖ = ‖x - O‖) (hne : x ≠ v3)
    (hpos : 0 < ⟪midpoint ℝ v3 x - a, midpoint ℝ v3 x - O⟫_ℝ) :
    0 < signedArea2 a v3 x * signedArea2 O v3 x := by
  have heq2 : ‖v3 - O‖ ^ 2 = ‖x - O‖ ^ 2 := by rw [heq]
  have hbridge := inner_midpoint_eq_signedArea_prod_of_chord_sphere v3 x a O heq2
  have hsq_pos : 0 < ‖x - v3‖ ^ 2 := by
    have : x - v3 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hprod_pos : 0 < signedArea2 O v3 x * signedArea2 a v3 x := by
    rw [← hbridge]; exact mul_pos hpos hsq_pos
  linarith [hprod_pos, mul_comm (signedArea2 O v3 x) (signedArea2 a v3 x)]
theorem inner_chord_eq_two_mul_inner_midpoint_off_sphere
    (v2 v3 v O : ℝ²) (heq : ‖v2 - O‖ ^ 2 = ‖v3 - O‖ ^ 2) :
    ⟪v2 - v, v3 - v⟫_ℝ
      = 2 * ⟪midpoint ℝ v2 v3 - O, midpoint ℝ v2 v3 - v⟫_ℝ
        + ‖v - O‖ ^ 2 - ‖v2 - O‖ ^ 2 := by
  have norm_sub_sq : ∀ (x y : ℝ²),
      ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := fun x y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply]
  have inner_eq : ∀ (a b : ℝ²),
      ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 := fun a b => by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two, mul_comm (a _) (b _)]
  have hmid : ∀ i : Fin 2, (midpoint ℝ v2 v3) i = ((v2 i + v3 i) : ℝ) / 2 := by
    intro i; rw [midpoint_eq_smul_add]
    simp [PiLp.smul_apply, PiLp.add_apply, invOf_eq_inv]; ring
  rw [norm_sub_sq v O, norm_sub_sq v2 O] at *
  rw [norm_sub_sq v3 O] at heq
  rw [inner_eq, inner_eq]
  simp only [PiLp.sub_apply, hmid] at *
  linarith
end Problem97
end Batch3N9
end Batch3N9Unit021

-- Original module: Solutions.Batch3N9.CircumscribedMECPacket
section Batch3N9Unit022
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open Finset
namespace Problem97
namespace MoserTriangle
variable {A : Finset ℝ²}
end MoserTriangle
namespace CircumscribedMECPacket
variable {A : Finset ℝ²}
end CircumscribedMECPacket
end Problem97
end Batch3N9
end Batch3N9Unit022

-- Original module: Solutions.Batch3N9.Dumitrescu.L2
section Batch3N9Unit023
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace Dumitrescu
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit023

-- Original module: Solutions.Batch3N9.Dumitrescu.Lc3
section Batch3N9Unit024
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace Dumitrescu
structure CapDiagonalVertexProfile (C : Finset ℝ²) where
  perApex : ℝ² → ℕ
  bound : ∀ a ∈ C, (Problem97.IsoscelesPairsAt C a).card ≤ perApex a
  sum_bound : 4 * (∑ a ∈ C, perApex a) ≤ (C.card - 1) ^ 2
namespace CapDiagonalVertexProfile
variable {C : Finset ℝ²}
end CapDiagonalVertexProfile
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit024

-- Original module: Solutions.Batch3N9.CGN.CGN
section Batch3N9Unit025
namespace Batch3N9
open scoped EuclideanGeometry
open scoped InnerProductSpace
open Finset
namespace Problem97
namespace CGN
namespace OrderedCap
variable {m : ℕ}
@[simp] theorem map_points (L : OrderedCap m) (T : ℝ² → ℝ²)
    (hT : Function.Injective T) (i : Fin m) :
    (L.map T hT).points i = T (L.points i) := rfl
namespace _root_.Problem97.CGN.OrderedCap
export _root_.Batch3N9.Problem97.CGN.OrderedCap (map_points)
end _root_.Problem97.CGN.OrderedCap
end OrderedCap
@[simp] theorem lastIndex_val {m : ℕ} (hm : 2 ≤ m) : (lastIndex hm).val = m - 1 := rfl
end CGN
end Problem97
end Batch3N9
end Batch3N9Unit025

-- Original module: Solutions.Batch3N9.SignedAreaOangle
section Batch3N9Unit026
namespace Batch3N9
open scoped EuclideanGeometry
namespace Problem97
theorem signedArea2_eq_stdOrientation_areaForm (v vj vk : ℝ²) :
    Problem97.signedArea2 v vj vk =
      stdOrientation.areaForm (vj - v) (vk - v) := by
  rw [stdOrientation, Orientation.areaForm_to_volumeForm,
      Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
      Module.Basis.det_apply]
  simp only [Module.Basis.toMatrix_apply, Matrix.det_fin_two, signedArea2,
             EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr,
             Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.sub_apply]
end Problem97
end Batch3N9
end Batch3N9Unit026

-- Original module: Solutions.Batch3N9.ConvexCyclicOrder.Basic
section Batch3N9Unit027
namespace Batch3N9
open scoped EuclideanGeometry
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit027

-- Original module: Solutions.Batch3N9.MEC.ArcAngle
section Batch3N9Unit028
namespace Batch3N9
open scoped EuclideanGeometry Real
namespace Problem97
theorem arcAngle_sub_arcAngle (center p q : ℝ²)
    (hp : p ≠ center) (hq : q ≠ center) :
    arcAngle center p - arcAngle center q =
      stdOrientation.oangle (q - center) (p - center) := by
  unfold arcAngle
  have he : (EuclideanSpace.basisFun (Fin 2) ℝ) 0 ≠ (0 : ℝ²) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero 0
  have hpv : p - center ≠ 0 := sub_ne_zero.mpr hp
  have hqv : q - center ≠ 0 := sub_ne_zero.mpr hq
  exact stdOrientation.oangle_sub_left he hqv hpv
theorem arcAngle_chord_length (center : ℝ²) (r : ℝ) (hr : 0 < r) (p q : ℝ²)
    (hp : dist p center = r) (hq : dist q center = r) :
    dist p q = 2 * r *
      |Real.sin ((arcAngle center p - arcAngle center q).toReal / 2)| := by
  have hp_ne : p ≠ center := by
    intro h; rw [h, dist_self] at hp; linarith
  have hq_ne : q ≠ center := by
    intro h; rw [h, dist_self] at hq; linarith
  have hu : ‖p - center‖ = r := by rw [← dist_eq_norm]; exact hp
  have hv : ‖q - center‖ = r := by rw [← dist_eq_norm]; exact hq
  have hpq : dist p q = ‖(p - center) - (q - center)‖ := by
    rw [dist_eq_norm]; congr 1; module
  have hcos : inner ℝ (p - center) (q - center)
            = r ^ 2 * (stdOrientation.oangle (p - center) (q - center)).cos := by
    rw [stdOrientation.inner_eq_norm_mul_norm_mul_cos_oangle (p - center) (q - center)]
    rw [hu, hv]; ring
  have hnsq : ‖(p - center) - (q - center)‖ ^ 2
            = 2 * r ^ 2 *
                (1 - (stdOrientation.oangle (p - center) (q - center)).cos) := by
    rw [norm_sub_sq_real, hu, hv, hcos]; ring
  have ha0 : arcAngle center p - arcAngle center q
           = stdOrientation.oangle (q - center) (p - center) :=
    arcAngle_sub_arcAngle center p q hp_ne hq_ne
  have hoangle_rev : stdOrientation.oangle (p - center) (q - center)
                  = -(stdOrientation.oangle (q - center) (p - center)) := by
    rw [stdOrientation.oangle_rev (q - center) (p - center)]
  have hcos_eq : (stdOrientation.oangle (p - center) (q - center)).cos
              = (arcAngle center p - arcAngle center q).cos := by
    rw [hoangle_rev, Real.Angle.cos_neg, ha0]
  have hcos_toReal : (arcAngle center p - arcAngle center q).cos
                  = Real.cos (arcAngle center p - arcAngle center q).toReal :=
    (Real.Angle.cos_toReal _).symm
  have hhalf : 1 - Real.cos (arcAngle center p - arcAngle center q).toReal
            = 2 * Real.sin ((arcAngle center p - arcAngle center q).toReal / 2) ^ 2 := by
    set x := (arcAngle center p - arcAngle center q).toReal
    have hcs := Real.cos_sq (x / 2)
    have h2 : (2 * (x / 2)) = x := by ring
    rw [h2] at hcs
    linarith [Real.sin_sq (x / 2)]
  have hsq : ‖(p - center) - (q - center)‖ ^ 2
          = (2 * r *
              |Real.sin ((arcAngle center p - arcAngle center q).toReal / 2)|) ^ 2 := by
    rw [hnsq, hcos_eq, hcos_toReal, hhalf]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  have h_nonneg_rhs : 0 ≤ 2 * r *
      |Real.sin ((arcAngle center p - arcAngle center q).toReal / 2)| := by
    refine mul_nonneg (mul_nonneg ?_ ?_) (abs_nonneg _)
    · norm_num
    · linarith
  rw [hpq]
  exact (pow_left_inj₀ (norm_nonneg _) h_nonneg_rhs two_ne_zero).mp hsq
theorem abs_sin_half_eq_iff (θ₁ θ₂ : Real.Angle) :
    |Real.sin (θ₁.toReal / 2)| = |Real.sin (θ₂.toReal / 2)| ↔
      |θ₁.toReal| = |θ₂.toReal| := by
  have habs₁ : |θ₁.toReal| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Real.Angle.neg_pi_lt_toReal _),
               Real.Angle.toReal_le_pi _⟩
  have habs₂ : |θ₂.toReal| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Real.Angle.neg_pi_lt_toReal _),
               Real.Angle.toReal_le_pi _⟩
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hdiv₁ : |θ₁.toReal / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have hdiv₂ : |θ₂.toReal / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hdiv₁,
      Real.abs_sin_eq_sin_abs_of_abs_le_pi hdiv₂]
  have hd₁ : |θ₁.toReal / 2| = |θ₁.toReal| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hd₂ : |θ₂.toReal / 2| = |θ₂.toReal| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [hd₁, hd₂]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hup₁ : |θ₁.toReal| / 2 ≤ Real.pi / 2 := by linarith
  have hup₂ : |θ₂.toReal| / 2 ≤ Real.pi / 2 := by linarith
  have hmem₁ : |θ₁.toReal| / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    refine ⟨?_, hup₁⟩
    have h0 : (0:ℝ) ≤ |θ₁.toReal| / 2 := by positivity
    have : -(Real.pi / 2) ≤ 0 := by linarith
    linarith
  have hmem₂ : |θ₂.toReal| / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    refine ⟨?_, hup₂⟩
    have h0 : (0:ℝ) ≤ |θ₂.toReal| / 2 := by positivity
    have : -(Real.pi / 2) ≤ 0 := by linarith
    linarith
  have : |θ₁.toReal| / 2 = |θ₂.toReal| / 2 := Real.injOn_sin hmem₁ hmem₂ h
  linarith
theorem arcAngle_chord_length_eq_iff
    (center : ℝ²) (r : ℝ) (hr : 0 < r)
    (p q₁ q₂ : ℝ²)
    (hp : dist p center = r) (hq₁ : dist q₁ center = r) (hq₂ : dist q₂ center = r) :
    dist p q₁ = dist p q₂ ↔
      |(arcAngle center p - arcAngle center q₁).toReal|
        = |(arcAngle center p - arcAngle center q₂).toReal| := by
  rw [arcAngle_chord_length center r hr p q₁ hp hq₁,
      arcAngle_chord_length center r hr p q₂ hp hq₂]
  have h2r_pos : 0 < 2 * r := by linarith
  have h2r_ne : (2 * r) ≠ 0 := ne_of_gt h2r_pos
  constructor
  · intro h
    have h' : |Real.sin ((arcAngle center p - arcAngle center q₁).toReal / 2)|
            = |Real.sin ((arcAngle center p - arcAngle center q₂).toReal / 2)| :=
      mul_left_cancel₀ h2r_ne h
    exact (abs_sin_half_eq_iff _ _).mp h'
  · intro h
    have h' : |Real.sin ((arcAngle center p - arcAngle center q₁).toReal / 2)|
            = |Real.sin ((arcAngle center p - arcAngle center q₂).toReal / 2)| :=
      (abs_sin_half_eq_iff _ _).mpr h
    rw [h']
end Problem97
end Batch3N9
end Batch3N9Unit028

-- Original module: Solutions.Batch3N9.Moser.NonDeg
section Batch3N9Unit029
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace MEC
lemma signedArea2_ne_zero_of_three_dist_eq {p₁ p₂ p₃ c : ℝ²} {r : ℝ}
    (h1 : dist p₁ c = r) (h2 : dist p₂ c = r) (h3 : dist p₃ c = r)
    (h12 : p₁ ≠ p₂) (h23 : p₂ ≠ p₃) (h13 : p₁ ≠ p₃) :
    Problem97.signedArea2 p₁ p₂ p₃ ≠ 0 := by
  intro hz
  exact not_collinear_of_three_dist_eq h1 h2 h3 h12 h23 h13
    (Problem97.collinear_of_signedArea2_eq_zero p₁ p₂ p₃ hz)
end MEC
end Problem97
end Batch3N9
end Batch3N9Unit029

-- Original module: Solutions.Batch3N9.ConvexCyclicOrder.Construct
section Batch3N9Unit030
namespace Batch3N9
open scoped EuclideanGeometry Real
namespace Problem97
theorem exists_center_interior_convexHull_of_convexIndep_noncoll
    {A : Finset ℝ²} (_hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∃ c : ℝ², c ∈ interior (convexHull ℝ (A : Set ℝ²)) := by
  have hspan : affineSpan ℝ (A : Set ℝ²) = ⊤ :=
    affineSpan_eq_top_of_not_collinear hnoncoll
  have hint : (interior (convexHull ℝ (A : Set ℝ²))).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  exact hint
theorem exists_isCcwConvexPolygon_of_convexIndep
    {A : Finset ℝ²} (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∃ (n : ℕ) (_ : 3 ≤ n) (phi : Fin n → ℝ²),
      Function.Injective phi ∧
      Finset.univ.image phi = A ∧
      EuclideanGeometry.IsCcwConvexPolygon phi := by
  obtain ⟨c, hc⟩ := Problem97.exists_center_interior_convexHull_of_convexIndep_noncoll hA hnoncoll
  obtain ⟨phi, hphi_inj, hphi_image, hphi_sorted⟩ :=
    Problem97.exists_cut_sorted_enumeration_of_convexIndep hA hc
  refine ⟨A.card, Problem97.three_le_card_of_convexIndep_noncoll hA hnoncoll, phi,
    hphi_inj, hphi_image, ?_⟩
  exact Problem97.isCcwConvexPolygon_of_cut_sorted_arcAngle
    hA hc hphi_inj hphi_image hphi_sorted
end Problem97
end Batch3N9
end Batch3N9Unit030

-- Original module: Solutions.Batch3N9.OangleBridge
section Batch3N9Unit031
namespace Batch3N9
open scoped EuclideanGeometry
namespace Problem97
namespace MEC
end MEC
end Problem97
end Batch3N9
end Batch3N9Unit031

-- Original module: Solutions.Batch3N9.CGN.CGN4g
section Batch3N9Unit032
namespace Batch3N9
open scoped EuclideanGeometry
open scoped InnerProductSpace
namespace Problem97
namespace CGN
theorem CGN4g0_globalBoundaryOrder_of_convexIndep
    {A : Finset ℝ²} (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∃ (n : ℕ) (_ : 3 ≤ n) (phi : Fin n → ℝ²),
      Function.Injective phi ∧
      Finset.univ.image phi = A ∧
      EuclideanGeometry.IsCcwConvexPolygon phi := by
  simpa using Problem97.exists_isCcwConvexPolygon_of_convexIndep hA hnoncoll
namespace StrictCapBlockData
variable {A C : Finset ℝ²}
theorem cap_image (B : StrictCapBlockData A C) :
    Finset.univ.image B.L.points = C :=
  B.Block.cap_image
namespace _root_.Problem97.CGN.StrictCapBlockData
export _root_.Batch3N9.Problem97.CGN.StrictCapBlockData (cap_image)
end _root_.Problem97.CGN.StrictCapBlockData
theorem cap_card_eq (B : StrictCapBlockData A C) : B.m = C.card := by
  have himageCard :
      (Finset.univ.image B.L.points).card = C.card := by
    rw [B.Block.cap_image]
  rw [Finset.card_image_of_injective _ B.L.injective] at himageCard
  simpa using himageCard
namespace _root_.Problem97.CGN.StrictCapBlockData
export _root_.Batch3N9.Problem97.CGN.StrictCapBlockData (cap_card_eq)
end _root_.Problem97.CGN.StrictCapBlockData
end StrictCapBlockData
end CGN
namespace CGN
theorem CGN4g_capData_of_supportCap_oriented
    {A C : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²))
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite M.v1 M.v2 M.v3 x)
    (hv_mem : M.v2 ∈ C)
    (hw_mem : M.v3 ∈ C)
    (P : Problem97.CircumscribedMECPacket A M)
    (hacute : 0 ≤ ⟪M.v2 - M.v1, M.v3 - M.v1⟫_ℝ) :
    ∃ m, ∃ L : OrderedCap m,
      ∃ Packet : MecCapPacket A L,
      ∃ Hside : MinorCapSideHypotheses Packet,
      ∃ Hord : StrictCapOrder A L,
        Finset.univ.image L.points = C ∧
          ((L.points (firstIndex Packet.hm) = M.v2 ∧
              L.points (lastIndex Packet.hm) = M.v3) ∨
            (L.points (firstIndex Packet.hm) = M.v3 ∧
              L.points (lastIndex Packet.hm) = M.v2)) := by
  rcases CGN4g_strictCapBlockData_of_supportCap_oriented
      (A := A) (C := C) (M := M) hA hnoncoll hC_subset hC_arc hv_mem hw_mem
      P hacute with
    ⟨B, horient⟩
  exact ⟨B.m, B.L, B.Packet, B.Hside, B.Hord, (_root_.Batch3N9.Problem97.CGN.StrictCapBlockData.cap_image B), horient⟩
end CGN
end Problem97
end Batch3N9
end Batch3N9Unit032

-- Original module: Solutions.Batch3N9.Dumitrescu.Lc1Strict
section Batch3N9Unit033
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open Finset
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit033

-- Original module: Solutions.Batch3N9.CGN.CGN6
section Batch3N9Unit034
namespace Batch3N9
open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators
namespace Problem97
namespace CGN
theorem CGN6b_nonacute_of_minorCapChainModel {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L) :
    ∀ {i j k : Fin m}, i < j → j < k →
      ⟪L.points i - L.points j, L.points k - L.points j⟫_ℝ ≤ 0 := by
  intro i j k hij hjk
  rw [M.points_eq i, M.points_eq j, M.points_eq k]
  exact CGN6b_nonacute_of_minorCapChainCoords M.coords hij hjk
theorem CGN6c_dist_strict_from_first {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L)
    {i0 : Fin m}
    (hi0 : i0 = finIndex m 0 (by
      have hm : 2 ≤ m := M.coords.hm
      omega)) :
    ∀ {r s : Fin m}, i0 < r → r < s →
      dist (L.points i0) (L.points r) <
        dist (L.points i0) (L.points s) := by
  subst i0
  intro r s h0r hrs
  let i0 : Fin m := finIndex m 0 (by
    have hm : 2 ≤ m := M.coords.hm
    omega)
  have hnonacute :
      ⟪L.points i0 - L.points r, L.points s - L.points r⟫_ℝ ≤ 0 :=
    CGN6b_nonacute_of_minorCapChainModel M h0r hrs
  have hinner_nonneg :
      0 ≤ ⟪L.points i0 - L.points r, L.points r - L.points s⟫_ℝ := by
    have hneg :
        ⟪L.points i0 - L.points r, L.points r - L.points s⟫_ℝ =
          -⟪L.points i0 - L.points r, L.points s - L.points r⟫_ℝ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (inner_neg_right (L.points i0 - L.points r) (L.points s - L.points r))
    rw [hneg]
    linarith
  have hrs_ne : L.points r ≠ L.points s := by
    intro h
    exact (ne_of_lt hrs) (L.injective h)
  have hrs_pos : 0 < dist (L.points r) (L.points s) := dist_pos.mpr hrs_ne
  have hsq_gap :
      dist (L.points i0) (L.points s) ^ 2 =
        dist (L.points i0) (L.points r) ^ 2 + dist (L.points r) (L.points s) ^ 2
          + 2 * ⟪L.points i0 - L.points r, L.points r - L.points s⟫_ℝ := by
    have hvec :
        L.points i0 - L.points s =
          (L.points i0 - L.points r) + (L.points r - L.points s) := by
      abel
    rw [dist_eq_norm, hvec, norm_add_pow_two_real, dist_eq_norm, dist_eq_norm]
    ring
  have hsq_lt :
      dist (L.points i0) (L.points r) ^ 2 <
        dist (L.points i0) (L.points s) ^ 2 := by
    have hrs_sq_pos : 0 < dist (L.points r) (L.points s) ^ 2 := by
      nlinarith only [hrs_pos, sq_pos_of_pos hrs_pos]
    nlinarith only [hinner_nonneg, hsq_gap, hrs_sq_pos]
  have hr_nonneg : 0 ≤ dist (L.points i0) (L.points r) := dist_nonneg
  have hs_nonneg : 0 ≤ dist (L.points i0) (L.points s) := dist_nonneg
  nlinarith only [hsq_lt, hr_nonneg, hs_nonneg, sq_nonneg (dist (L.points i0) (L.points r) - dist (L.points i0) (L.points s)), sq_nonneg (dist (L.points i0) (L.points r) + dist (L.points i0) (L.points s))]

theorem CGN6c_dist_strict_from_last {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L)
    {jm : Fin m}
    (hjm : jm = finIndex m (m - 1) (by
      have hm : 2 ≤ m := M.coords.hm
      omega)) :
    ∀ {r s : Fin m}, r < s → s < jm →
      dist (L.points jm) (L.points s) <
        dist (L.points jm) (L.points r) := by
  subst jm
  intro r s hrs hsj
  let jm : Fin m := finIndex m (m - 1) (by
    have hm : 2 ≤ m := M.coords.hm
    omega)
  have hnonacute :
      ⟪L.points r - L.points s, L.points jm - L.points s⟫_ℝ ≤ 0 :=
    CGN6b_nonacute_of_minorCapChainModel M hrs hsj
  have hinner_nonneg :
      0 ≤ ⟪L.points jm - L.points s, L.points s - L.points r⟫_ℝ := by
    have hnonacute' :
        ⟪L.points jm - L.points s, L.points r - L.points s⟫_ℝ ≤ 0 := by
      simpa [real_inner_comm] using hnonacute
    have hneg :
        ⟪L.points jm - L.points s, L.points s - L.points r⟫_ℝ =
          -⟪L.points jm - L.points s, L.points r - L.points s⟫_ℝ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (inner_neg_right (L.points jm - L.points s) (L.points r - L.points s))
    rw [hneg]
    linarith
  have hrs_ne : L.points r ≠ L.points s := by
    intro h
    exact (ne_of_lt hrs) (L.injective h)
  have hrs_pos : 0 < dist (L.points r) (L.points s) := dist_pos.mpr hrs_ne
  have hsq_gap :
      dist (L.points jm) (L.points r) ^ 2 =
        dist (L.points jm) (L.points s) ^ 2 + dist (L.points r) (L.points s) ^ 2
          + 2 * ⟪L.points jm - L.points s, L.points s - L.points r⟫_ℝ := by
    have hvec :
        L.points jm - L.points r =
          (L.points jm - L.points s) + (L.points s - L.points r) := by
      abel
    rw [dist_eq_norm, hvec, norm_add_pow_two_real, dist_eq_norm, dist_eq_norm]
    have hnorm_rev : ‖L.points s - L.points r‖ ^ 2 = ‖L.points r - L.points s‖ ^ 2 := by
      rw [norm_sub_rev]
    nlinarith only [hnorm_rev]
  have hsq_lt :
      dist (L.points jm) (L.points s) ^ 2 <
        dist (L.points jm) (L.points r) ^ 2 := by
    have hrs_sq_pos : 0 < dist (L.points r) (L.points s) ^ 2 := by
      nlinarith only [hrs_pos, sq_pos_of_pos hrs_pos]
    nlinarith only [hinner_nonneg, hsq_gap, hrs_sq_pos]
  have hs_nonneg : 0 ≤ dist (L.points jm) (L.points s) := dist_nonneg
  have hr_nonneg : 0 ≤ dist (L.points jm) (L.points r) := dist_nonneg
  nlinarith only [hsq_lt, hs_nonneg, hr_nonneg, sq_nonneg (dist (L.points jm) (L.points s) - dist (L.points jm) (L.points r)), sq_nonneg (dist (L.points jm) (L.points s) + dist (L.points jm) (L.points r))]

end CGN
end Problem97
end Batch3N9
end Batch3N9Unit034

-- Original module: Solutions.Batch3N9.CGN.CGN7
section Batch3N9Unit035
namespace Batch3N9
open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators
open Finset
namespace Problem97
namespace CGN
end CGN
end Problem97
end Batch3N9
end Batch3N9Unit035

-- Original module: Solutions.Batch3N9.ArcPartitionCount
section Batch3N9Unit036
namespace Batch3N9
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace MEC
end MEC
end Problem97
end Batch3N9
end Batch3N9Unit036

-- Original module: Solutions.Batch3N9.Dumitrescu.L4
section Batch3N9Unit037
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace Dumitrescu
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit037

-- Original module: Solutions.Batch3N9.Dumitrescu.L7
section Batch3N9Unit038
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace Dumitrescu
def IsCrossCapEdge {A : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (CP : Problem97.CapTriple A M) (uv : Finset ℝ²) : Prop :=
  uv ⊆ A ∧ uv.card = 2 ∧
    ¬ uv ⊆ CP.C1 ∧ ¬ uv ⊆ CP.C2 ∧ ¬ uv ⊆ CP.C3
lemma IsCrossCapEdge.card_eq_two
    {A : Finset ℝ²} {M : Problem97.MoserTriangle A}
    {CP : Problem97.CapTriple A M} {uv : Finset ℝ²}
    (h : IsCrossCapEdge CP uv) : uv.card = 2 := h.2.1
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit038

-- Original module: Solutions.Batch3N9.Dumitrescu.L10
section Batch3N9Unit039
namespace Batch3N9
set_option linter.style.openClassical false
open scoped EuclideanGeometry
open Finset Classical
namespace Problem97
namespace Dumitrescu
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit039

-- Original module: Solutions.Batch3N9.Dumitrescu.L9
section Batch3N9Unit040
namespace Batch3N9
namespace Problem97
namespace Dumitrescu
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit040

-- Original module: Solutions.Batch3N9.Dumitrescu.L10c
section Batch3N9Unit041
namespace Batch3N9
namespace Problem97
namespace Dumitrescu
end Dumitrescu
end Problem97
end Batch3N9
end Batch3N9Unit041

-- Original module: Solutions.Batch3N9.CGN.CGN8
section Batch3N9Unit042
namespace Batch3N9
open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators
open Finset
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit042

-- Original module: Solutions.Batch3N9.Counting
section Batch3N9Unit043
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
theorem not_collinear_of_K4 {A : Finset ℝ²} (hne : A.Nonempty)
    (hconv : ConvexIndep A) (hK4 : HasNEquidistantProperty 4 A) :
    ¬ Collinear ℝ (A : Set ℝ²) := by
  have h5 : 5 ≤ A.card := card_ge_five_of_K4 hne hK4
  have h3 : 3 ≤ A.card := le_trans (by decide : 3 ≤ 5) h5
  exact ConvexIndep.not_collinear_of_card_ge_three hconv h3
theorem boundary_card_ge_three_of_K4 {A : Finset ℝ²} (hne : A.Nonempty)
    (hconv : ConvexIndep A) (hK4 : HasNEquidistantProperty 4 A) :
    3 ≤ (A.filter (fun p =>
      dist p (Problem97.MEC.mec A hne).center = (Problem97.MEC.mec A hne).radius)).card := by
  have hnoncol : ¬ Collinear ℝ (A : Set ℝ²) :=
    not_collinear_of_K4 hne hconv hK4
  exact Problem97.MEC.no_diameter_under_k4 hne hnoncol hconv hK4
end Problem97
end Batch3N9
end Batch3N9Unit043

-- Original module: Solutions.Batch3N9.N9Endpoint.N4a
section Batch3N9Unit044
namespace Batch3N9
open scoped EuclideanGeometry
open scoped InnerProductSpace
open Finset
namespace Problem97
namespace FiniteEndpoint
structure OrderedSideChain (m : ℕ) where
  points : Fin m → ℝ²
  injective : Function.Injective points
namespace OrderedSideChain
variable {m : ℕ}
noncomputable def support (L : OrderedSideChain m) : Finset ℝ² :=
  Finset.univ.image L.points
@[simp] theorem mem_support_iff {L : OrderedSideChain m} {x : ℝ²} :
    x ∈ L.support ↔ ∃ i : Fin m, L.points i = x := by
  classical
  unfold support
  simp
theorem b3n9m044_card_filter_eqDist_le_one
    (center : ℝ²) (L : OrderedSideChain m)
    (hmono : ∀ {i j : Fin m}, i < j → dist center (L.points i) < dist center (L.points j))
    (r : ℝ) :
    (Finset.univ.filter (fun i => dist center (L.points i) = r)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi j hj
  by_cases hij : i = j
  · exact hij
  · rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
    · have hdi : dist center (L.points i) = r := (Finset.mem_filter.mp hi).2
      have hdj : dist center (L.points j) = r := (Finset.mem_filter.mp hj).2
      have hlt := hmono hij_lt
      rw [hdi, hdj] at hlt
      exact (False.elim (lt_irrefl r hlt))
    · have hdi : dist center (L.points i) = r := (Finset.mem_filter.mp hi).2
      have hdj : dist center (L.points j) = r := (Finset.mem_filter.mp hj).2
      have hlt := hmono hji_lt
      rw [hdj, hdi] at hlt
      exact (False.elim (lt_irrefl r hlt))
theorem card_support_filter_eqDist_le_one
    (center : ℝ²) (L : OrderedSideChain m)
    (hmono : ∀ {i j : Fin m}, i < j → dist center (L.points i) < dist center (L.points j))
    (r : ℝ) :
    (L.support.filter (fun x => dist center x = r)).card ≤ 1 := by
  classical
  have hrepr :
      L.support.filter (fun x => dist center x = r)
        = (Finset.univ.filter (fun i => dist center (L.points i) = r)).image L.points := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hx_support, hx_dist⟩
      rcases (mem_support_iff.mp hx_support) with ⟨i, rfl⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx_dist⟩, rfl⟩
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      exact Finset.mem_filter.mpr ⟨mem_support_iff.mpr ⟨i, rfl⟩, (Finset.mem_filter.mp hi).2⟩
  rw [hrepr]
  rw [Finset.card_image_of_injective _ L.injective]
  exact b3n9m044_card_filter_eqDist_le_one center L hmono r
theorem card_le_one_of_subset_sameRadius
    (center : ℝ²) (L : OrderedSideChain m)
    (hmono : ∀ {i j : Fin m}, i < j → dist center (L.points i) < dist center (L.points j))
    {T : Finset ℝ²} (r : ℝ)
    (hsub : T ⊆ L.support)
    (hrad : ∀ x ∈ T, dist center x = r) :
    T.card ≤ 1 := by
  have hsub' : T ⊆ L.support.filter (fun x => dist center x = r) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hsub hx, hrad x hx⟩
  exact le_trans (Finset.card_le_card hsub') (card_support_filter_eqDist_le_one center L hmono r)
end OrderedSideChain
noncomputable def OrderedSideChain.ofOrderedCap {m : ℕ}
    (L : Problem97.CGN.OrderedCap m) : OrderedSideChain m where
  points := L.points
  injective := L.injective
@[simp] theorem OrderedSideChain.ofOrderedCap_points {m : ℕ}
    (L : Problem97.CGN.OrderedCap m) (i : Fin m) :
    (OrderedSideChain.ofOrderedCap L).points i = L.points i := rfl
noncomputable def OrderedSideChain.ofOrderedCapRev {m : ℕ}
    (L : Problem97.CGN.OrderedCap m) : OrderedSideChain m where
  points := fun i => L.points i.rev
  injective := by
    intro i j hij
    apply Fin.rev_injective
    exact L.injective hij
@[simp] theorem OrderedSideChain.ofOrderedCapRev_points {m : ℕ}
    (L : Problem97.CGN.OrderedCap m) (i : Fin m) :
    (OrderedSideChain.ofOrderedCapRev L).points i = L.points i.rev := rfl
@[simp] theorem OrderedSideChain.mem_support_ofOrderedCapRev_iff {m : ℕ}
    (L : Problem97.CGN.OrderedCap m) {x : ℝ²} :
    x ∈ (OrderedSideChain.ofOrderedCapRev L).support ↔ ∃ i : Fin m, L.points i = x := by
  constructor
  · intro hx
    rcases OrderedSideChain.mem_support_iff.mp hx with ⟨i, hi⟩
    refine ⟨i.rev, ?_⟩
    simpa using hi
  · intro hx
    rcases hx with ⟨i, hi⟩
    refine OrderedSideChain.mem_support_iff.mpr ⟨i.rev, ?_⟩
    simpa using hi
@[simp] theorem OrderedSideChain.support_ofOrderedCapRev {m : ℕ}
    (L : Problem97.CGN.OrderedCap m) :
    (OrderedSideChain.ofOrderedCapRev L).support = Finset.univ.image L.points := by
  ext x
  constructor
  · intro hx
    rcases (OrderedSideChain.mem_support_ofOrderedCapRev_iff (L := L)).1 hx with ⟨i, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, -, hi⟩
    exact (OrderedSideChain.mem_support_ofOrderedCapRev_iff (L := L)).2 ⟨i, hi⟩
abbrev E3L20a_leftEndpoint_capDistance_strict
    (center : ℝ²) {m : ℕ} (L : OrderedSideChain m) : Prop :=
  ∀ {i j : Fin m}, i < j → dist center (L.points i) < dist center (L.points j)
abbrev E3L20b_rightEndpoint_capDistance_strict
    (center : ℝ²) {m : ℕ} (L : OrderedSideChain m) : Prop :=
  ∀ {i j : Fin m}, i < j → dist center (L.points i) < dist center (L.points j)
theorem b3n9m044_strict_from_first_of_cgnCapData
    {A : Finset ℝ²} {m : ℕ} {L : Problem97.CGN.OrderedCap m}
    (Packet : Problem97.CGN.MecCapPacket A L)
    (Hside : Problem97.CGN.MinorCapSideHypotheses Packet)
    (Hord : Problem97.CGN.StrictCapOrder A L) :
    E3L20a_leftEndpoint_capDistance_strict
      (L.points (Problem97.CGN.firstIndex Packet.hm))
      (OrderedSideChain.ofOrderedCap L) := by
  classical
  obtain ⟨T, hT, tau, hModelT⟩ :=
    Problem97.CGN.CGN6norm_minorCapChainModel_of_mecCapPacket Packet Hside Hord
  let LT : Problem97.CGN.OrderedCap m := L.map T hT
  let ModelT : Problem97.CGN.MinorCapChainModel LT := Classical.choice hModelT
  intro i j hij
  by_cases hi0 : i = Problem97.CGN.firstIndex Packet.hm
  · subst hi0
    have hne : L.points (Problem97.CGN.firstIndex Packet.hm) ≠ L.points j := by
      intro h
      exact (ne_of_lt hij) (L.injective h)
    have hdist_pos : 0 < dist (L.points (Problem97.CGN.firstIndex Packet.hm)) (L.points j) :=
      dist_pos.mpr hne
    simpa [OrderedSideChain.ofOrderedCap] using hdist_pos
  · have hi_val_ne_zero : i.val ≠ 0 := by
      intro hi_val_zero
      apply hi0
      ext
      simpa [Problem97.CGN.firstIndex, Problem97.CGN.finIndex] using hi_val_zero
    have h0i_val : 0 < i.val := Nat.pos_of_ne_zero hi_val_ne_zero
    have h0i : Problem97.CGN.firstIndex Packet.hm < i := by
      exact Fin.lt_def.mpr (by
        simpa [Problem97.CGN.firstIndex, Problem97.CGN.finIndex] using h0i_val)
    have hi0eq : Problem97.CGN.firstIndex Packet.hm =
        Problem97.CGN.finIndex m 0 (by
          have hm : 2 ≤ m := ModelT.coords.hm
          omega) := by
      ext
      simp [Problem97.CGN.firstIndex, Problem97.CGN.finIndex]
    have himg :
        dist (T (L.points (Problem97.CGN.firstIndex Packet.hm))) (T (L.points i)) <
          dist (T (L.points (Problem97.CGN.firstIndex Packet.hm))) (T (L.points j)) := by
      simpa [LT, Problem97.CGN.OrderedCap.map_points] using
        (Problem97.CGN.CGN6c_dist_strict_from_first
          (M := ModelT) (i0 := Problem97.CGN.firstIndex Packet.hm) hi0eq
          (r := i) (s := j) h0i hij)
    have horig :
        dist (L.points (Problem97.CGN.firstIndex Packet.hm)) (L.points i) <
          dist (L.points (Problem97.CGN.firstIndex Packet.hm)) (L.points j) := by
      rw [tau.dist_image, tau.dist_image] at himg
      nlinarith only [himg, tau.scale_pos]
    simpa [OrderedSideChain.ofOrderedCap] using horig
theorem b3n9m044_strict_from_last_of_cgnCapData
    {A : Finset ℝ²} {m : ℕ} {L : Problem97.CGN.OrderedCap m}
    (Packet : Problem97.CGN.MecCapPacket A L)
    (Hside : Problem97.CGN.MinorCapSideHypotheses Packet)
    (Hord : Problem97.CGN.StrictCapOrder A L) :
    E3L20b_rightEndpoint_capDistance_strict
      (L.points (Problem97.CGN.lastIndex Packet.hm))
      (OrderedSideChain.ofOrderedCapRev L) := by
  classical
  obtain ⟨T, hT, tau, hModelT⟩ :=
    Problem97.CGN.CGN6norm_minorCapChainModel_of_mecCapPacket Packet Hside Hord
  let LT : Problem97.CGN.OrderedCap m := L.map T hT
  let ModelT : Problem97.CGN.MinorCapChainModel LT := Classical.choice hModelT
  intro i j hij
  by_cases hi0 : i = Problem97.CGN.firstIndex Packet.hm
  · subst hi0
    have hj0 : j ≠ Problem97.CGN.firstIndex Packet.hm := ne_of_gt hij
    have hj_val_ne_zero : j.val ≠ 0 := by
      intro hj_val_zero
      apply hj0
      ext
      simpa [Problem97.CGN.firstIndex] using hj_val_zero
    have hrev_last : (Problem97.CGN.firstIndex Packet.hm).rev =
        Problem97.CGN.lastIndex Packet.hm := by
      ext
      simp [Problem97.CGN.firstIndex, Problem97.CGN.lastIndex, Fin.val_rev]
    have hne : L.points (Problem97.CGN.lastIndex Packet.hm) ≠ L.points j.rev := by
      intro h
      have hidx : j.rev = Problem97.CGN.lastIndex Packet.hm := L.injective h.symm
      have hidx_val : (j.rev).val = (Problem97.CGN.lastIndex Packet.hm).val := congrArg Fin.val hidx
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val] at hidx_val
      have hj_val_zero : j.val = 0 := by omega
      exact hj_val_ne_zero hj_val_zero
    have hdist_pos : 0 < dist (L.points (Problem97.CGN.lastIndex Packet.hm)) (L.points j.rev) :=
      dist_pos.mpr hne
    rw [show (OrderedSideChain.ofOrderedCapRev L).points (Problem97.CGN.firstIndex Packet.hm) =
        L.points (Problem97.CGN.lastIndex Packet.hm) by
          simpa [OrderedSideChain.ofOrderedCapRev_points] using congrArg L.points hrev_last]
    simpa [OrderedSideChain.ofOrderedCapRev_points] using hdist_pos
  · have hi_val_ne_zero : i.val ≠ 0 := by
      intro hi_val_zero
      apply hi0
      ext
      simpa [Problem97.CGN.firstIndex] using hi_val_zero
    have hrev_lt : j.rev < i.rev := by
      apply Fin.lt_def.mpr
      have hij_val : i.val < j.val := Fin.lt_def.mp hij
      rw [Fin.val_rev, Fin.val_rev]
      omega
    have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
      apply Fin.lt_def.mpr
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
      omega
    have hjmeq : Problem97.CGN.lastIndex Packet.hm =
        Problem97.CGN.finIndex m (m - 1) (by
          have hm : 2 ≤ m := ModelT.coords.hm
          omega) := by
      ext
      simp [Problem97.CGN.lastIndex, Problem97.CGN.finIndex]
    have himg :
        dist (T (L.points (Problem97.CGN.lastIndex Packet.hm))) (T (L.points i.rev)) <
          dist (T (L.points (Problem97.CGN.lastIndex Packet.hm))) (T (L.points j.rev)) := by
      simpa [LT, Problem97.CGN.OrderedCap.map_points] using
        (Problem97.CGN.CGN6c_dist_strict_from_last
          (M := ModelT) (jm := Problem97.CGN.lastIndex Packet.hm) hjmeq
          (r := j.rev) (s := i.rev) hrev_lt hi_rev_lt_last)
    have horig :
        dist (L.points (Problem97.CGN.lastIndex Packet.hm)) (L.points i.rev) <
          dist (L.points (Problem97.CGN.lastIndex Packet.hm)) (L.points j.rev) := by
      rw [tau.dist_image, tau.dist_image] at himg
      nlinarith only [himg, tau.scale_pos]
    simpa [OrderedSideChain.ofOrderedCapRev_points] using horig
theorem E3L20a_of_cgnCapData
    {A : Finset ℝ²} {m : ℕ} {L : Problem97.CGN.OrderedCap m}
    (Packet : Problem97.CGN.MecCapPacket A L)
    (Hside : Problem97.CGN.MinorCapSideHypotheses Packet)
    (Hord : Problem97.CGN.StrictCapOrder A L) :
    E3L20a_leftEndpoint_capDistance_strict
      (L.points (Problem97.CGN.firstIndex Packet.hm))
      (OrderedSideChain.ofOrderedCap L) :=
  b3n9m044_strict_from_first_of_cgnCapData Packet Hside Hord
theorem E3L20b_of_cgnCapData
    {A : Finset ℝ²} {m : ℕ} {L : Problem97.CGN.OrderedCap m}
    (Packet : Problem97.CGN.MecCapPacket A L)
    (Hside : Problem97.CGN.MinorCapSideHypotheses Packet)
    (Hord : Problem97.CGN.StrictCapOrder A L) :
    E3L20b_rightEndpoint_capDistance_strict
      (L.points (Problem97.CGN.lastIndex Packet.hm))
      (OrderedSideChain.ofOrderedCapRev L) :=
  b3n9m044_strict_from_last_of_cgnCapData Packet Hside Hord
theorem one_hit_sameRadius_at_v2_of_supportCap
    {A C : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²))
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite M.v1 M.v2 M.v3 x)
    (hv_mem : M.v2 ∈ C)
    (hw_mem : M.v3 ∈ C)
    (P : Problem97.CircumscribedMECPacket A M)
    (hacute : 0 ≤ ⟪M.v2 - M.v1, M.v3 - M.v1⟫_ℝ)
    {S : Finset ℝ²} {r : ℝ}
    (hsub : S ⊆ C)
    (hrad : ∀ x ∈ S, dist M.v2 x = r) :
    S.card ≤ 1 := by
  classical
  rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
      (A := A) (C := C) (M := M) hA hnoncoll hC_subset hC_arc hv_mem hw_mem P hacute with
    ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
  rcases hEnds with hFirstLast | hLastFirst
  · have hmono :
        E3L20a_leftEndpoint_capDistance_strict
          (L.points (Problem97.CGN.firstIndex Packet.hm))
          (OrderedSideChain.ofOrderedCap L) := by
      intro i j hij
      exact E3L20a_of_cgnCapData Packet Hside Hord hij
    have hsubL : S ⊆ (OrderedSideChain.ofOrderedCap L).support := by
      intro x hx
      simpa [OrderedSideChain.support, OrderedSideChain.ofOrderedCap, hLC] using hsub hx
    have hradL : ∀ x ∈ S, dist (L.points (Problem97.CGN.firstIndex Packet.hm)) x = r := by
      intro x hx
      simpa [hFirstLast.1] using hrad x hx
    exact OrderedSideChain.card_le_one_of_subset_sameRadius
      (L.points (Problem97.CGN.firstIndex Packet.hm))
      (OrderedSideChain.ofOrderedCap L) hmono r hsubL hradL
  · have hmono :
        E3L20b_rightEndpoint_capDistance_strict
          (L.points (Problem97.CGN.lastIndex Packet.hm))
          (OrderedSideChain.ofOrderedCapRev L) := by
      intro i j hij
      exact E3L20b_of_cgnCapData Packet Hside Hord hij
    have hsubL : S ⊆ (OrderedSideChain.ofOrderedCapRev L).support := by
      intro x hx
      rw [OrderedSideChain.support_ofOrderedCapRev, hLC]
      exact hsub hx
    have hradL : ∀ x ∈ S, dist (L.points (Problem97.CGN.lastIndex Packet.hm)) x = r := by
      intro x hx
      simpa [hLastFirst.2] using hrad x hx
    exact OrderedSideChain.card_le_one_of_subset_sameRadius
      (L.points (Problem97.CGN.lastIndex Packet.hm))
      (OrderedSideChain.ofOrderedCapRev L) hmono r hsubL hradL
theorem one_hit_sameRadius_at_v3_of_supportCap
    {A C : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²))
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite M.v1 M.v2 M.v3 x)
    (hv_mem : M.v2 ∈ C)
    (hw_mem : M.v3 ∈ C)
    (P : Problem97.CircumscribedMECPacket A M)
    (hacute : 0 ≤ ⟪M.v2 - M.v1, M.v3 - M.v1⟫_ℝ)
    {S : Finset ℝ²} {r : ℝ}
    (hsub : S ⊆ C)
    (hrad : ∀ x ∈ S, dist M.v3 x = r) :
    S.card ≤ 1 := by
  classical
  rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
      (A := A) (C := C) (M := M) hA hnoncoll hC_subset hC_arc hv_mem hw_mem P hacute with
    ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
  rcases hEnds with hFirstLast | hLastFirst
  · have hmono :
        E3L20b_rightEndpoint_capDistance_strict
          (L.points (Problem97.CGN.lastIndex Packet.hm))
          (OrderedSideChain.ofOrderedCapRev L) := by
      intro i j hij
      exact E3L20b_of_cgnCapData Packet Hside Hord hij
    have hsubL : S ⊆ (OrderedSideChain.ofOrderedCapRev L).support := by
      intro x hx
      rw [OrderedSideChain.support_ofOrderedCapRev, hLC]
      exact hsub hx
    have hradL : ∀ x ∈ S, dist (L.points (Problem97.CGN.lastIndex Packet.hm)) x = r := by
      intro x hx
      simpa [hFirstLast.2] using hrad x hx
    exact OrderedSideChain.card_le_one_of_subset_sameRadius
      (L.points (Problem97.CGN.lastIndex Packet.hm))
      (OrderedSideChain.ofOrderedCapRev L) hmono r hsubL hradL
  · have hmono :
        E3L20a_leftEndpoint_capDistance_strict
          (L.points (Problem97.CGN.firstIndex Packet.hm))
          (OrderedSideChain.ofOrderedCap L) := by
      intro i j hij
      exact E3L20a_of_cgnCapData Packet Hside Hord hij
    have hsubL : S ⊆ (OrderedSideChain.ofOrderedCap L).support := by
      intro x hx
      simpa [OrderedSideChain.support, OrderedSideChain.ofOrderedCap, hLC] using hsub hx
    have hradL : ∀ x ∈ S, dist (L.points (Problem97.CGN.firstIndex Packet.hm)) x = r := by
      intro x hx
      simpa [hLastFirst.1] using hrad x hx
    exact OrderedSideChain.card_le_one_of_subset_sameRadius
      (L.points (Problem97.CGN.firstIndex Packet.hm))
      (OrderedSideChain.ofOrderedCap L) hmono r hsubL hradL
end FiniteEndpoint
end Problem97
end Batch3N9
end Batch3N9Unit044

-- Original module: Solutions.Batch3N9.N9Endpoint.Shell
section Batch3N9Unit045
set_option backward.isDefEq.respectTransparency false
namespace Batch3N9
open scoped EuclideanGeometry
open scoped InnerProductSpace
open Finset
namespace Problem97
namespace FiniteEndpointShell
theorem hcapSum
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.CP.C1.card + S.CP.C2.card + S.CP.C3.card = A.card + 3 := by
  rw [S.hcard9]
  norm_num [S.hcapSum12]
theorem k4_at_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    HasNEquidistantPointsAt 4 A S.MT.toMoserTriangle.v1 :=
  S.hK4 _ S.MT.toMoserTriangle.v1_mem
theorem k4_at_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    HasNEquidistantPointsAt 4 A S.MT.toMoserTriangle.v2 :=
  S.hK4 _ S.MT.toMoserTriangle.v2_mem
theorem k4_at_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    HasNEquidistantPointsAt 4 A S.MT.toMoserTriangle.v3 :=
  S.hK4 _ S.MT.toMoserTriangle.v3_mem
theorem I1_card_ge_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    2 ≤ S.I1.card := by
  classical
  rcases S.k4_at_v1 with ⟨r, hrpos, hTcard⟩
  let T : Finset ℝ² := A.filter (fun x => dist S.triangle.v1 x = r)
  have hv1_not_mem_T : S.triangle.v1 ∉ T := by
    intro hv1T
    have hv1eq : dist S.triangle.v1 S.triangle.v1 = r := (Finset.mem_filter.mp hv1T).2
    have h0r : (0 : ℝ) = r := by simpa using hv1eq
    nlinarith only [hrpos, h0r]
  have hC2_one : (T ∩ S.CP.C2).card ≤ 1 := by
    apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v3_of_supportCap
      (A := A) (C := S.CP.C2) (M := S.triangle2)
      S.hconv S.hnoncol S.CP.C2_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.1)
      S.CP.v3_mem_C2 S.CP.v1_mem_C2 S.packet2 S.packet2.inner_at_v1
      (S := T ∩ S.CP.C2) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
  have hC3_one : (T ∩ S.CP.C3).card ≤ 1 := by
    apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v2_of_supportCap
      (A := A) (C := S.CP.C3) (M := S.triangle3)
      S.hconv S.hnoncol S.CP.C3_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.2)
      S.CP.v1_mem_C3 S.CP.v2_mem_C3 S.packet3 S.packet3.inner_at_v1
      (S := T ∩ S.CP.C3) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
  have hcover :
      T \ S.I1 ⊆ (T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3) := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnotI1⟩
    have hxA : x ∈ A := (Finset.mem_filter.mp hxT).1
    by_cases hxv3 : x = S.triangle.v3
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv3] using S.CP.v3_mem_C2⟩
    by_cases hxv2 : x = S.triangle.v2
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv2] using S.CP.v2_mem_C3⟩
    by_cases hxv1 : x = S.triangle.v1
    · exact False.elim (hv1_not_mem_T (hxv1 ▸ hxT))
    have hxnonmoser : x ∉ S.triangle.verts := by
      simp [Problem97.MoserTriangle.verts, hxv1, hxv2, hxv3]
    have hxnotC1 : x ∉ S.CP.C1 := by
      intro hxC1
      have hxI1 : x ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hxv3, Finset.mem_erase.mpr ⟨hxv2, hxC1⟩⟩
      exact hxnotI1 hxI1
    have hone := S.CP.nonmoser_in_one x hxA hxnonmoser
    by_cases hxC2 : x ∈ S.CP.C2
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hxT, hxC2⟩
    · have hxC3 : x ∈ S.CP.C3 := by
        by_cases hxC3 : x ∈ S.CP.C3
        · exact hxC3
        · have : (0 : ℕ) = 1 := by
            simpa [hxnotC1, hxC2, hxC3] using hone
          omega
      apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxT, hxC3⟩
  have houtside_le :
      (T \ S.I1).card ≤ 2 := by
    calc
      (T \ S.I1).card ≤ ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card := Finset.card_le_card hcover
      _ ≤ (T ∩ S.CP.C2).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by omega
      _ = 2 := by norm_num
  have hsplit : (T \ S.I1).card + (T ∩ S.I1).card = T.card := by
    simpa [Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I1
  have hinter_le : (T ∩ S.I1).card ≤ S.I1.card := Finset.card_le_card Finset.inter_subset_right
  have hTfour : 4 ≤ T.card := by
    show 4 ≤ (A.filter (fun q => dist S.MT.toMoserTriangle.v1 q = r)).card
    exact hTcard
  omega
theorem I2_card_ge_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    2 ≤ S.I2.card := by
  classical
  rcases S.k4_at_v2 with ⟨r, hrpos, hTcard⟩
  let T : Finset ℝ² := A.filter (fun x => dist S.triangle.v2 x = r)
  have hv2_not_mem_T : S.triangle.v2 ∉ T := by
    intro hv2T
    have hv2eq : dist S.triangle.v2 S.triangle.v2 = r := (Finset.mem_filter.mp hv2T).2
    have h0r : (0 : ℝ) = r := by simpa using hv2eq
    nlinarith only [hrpos, h0r]
  have hC1_one : (T ∩ S.CP.C1).card ≤ 1 := by
    apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v2_of_supportCap
      (A := A) (C := S.CP.C1) (M := S.triangle)
      S.hconv S.hnoncol S.CP.C1_subset
      (fun x hxA => (S.CP.arc_membership x hxA).1)
      S.CP.v2_mem_C1 S.CP.v3_mem_C1 S.Packet S.Packet.inner_at_v1
      (S := T ∩ S.CP.C1) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      simpa using (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
  have hC3_one : (T ∩ S.CP.C3).card ≤ 1 := by
    apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v3_of_supportCap
      (A := A) (C := S.CP.C3) (M := S.triangle3)
      S.hconv S.hnoncol S.CP.C3_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.2)
      S.CP.v1_mem_C3 S.CP.v2_mem_C3 S.packet3 S.packet3.inner_at_v1
      (S := T ∩ S.CP.C3) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
  have hcover :
      T \ S.I2 ⊆ (T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3) := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnotI2⟩
    have hxA : x ∈ A := (Finset.mem_filter.mp hxT).1
    by_cases hxv1 : x = S.triangle.v1
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv1] using S.CP.v1_mem_C3⟩
    by_cases hxv3 : x = S.triangle.v3
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv3] using S.CP.v3_mem_C1⟩
    by_cases hxv2 : x = S.triangle.v2
    · exact False.elim (hv2_not_mem_T (hxv2 ▸ hxT))
    have hxnonmoser : x ∉ S.triangle.verts := by
      simp [Problem97.MoserTriangle.verts, hxv1, hxv2, hxv3]
    have hxnotC2 : x ∉ S.CP.C2 := by
      intro hxC2
      have hxI2 : x ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hxv1, Finset.mem_erase.mpr ⟨hxv3, hxC2⟩⟩
      exact hxnotI2 hxI2
    have hone := S.CP.nonmoser_in_one x hxA hxnonmoser
    by_cases hxC1 : x ∈ S.CP.C1
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hxT, hxC1⟩
    · have hxC3 : x ∈ S.CP.C3 := by
        by_cases hxC3 : x ∈ S.CP.C3
        · exact hxC3
        · have : (0 : ℕ) = 1 := by
            simpa [hxC1, hxnotC2, hxC3] using hone
          omega
      apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxT, hxC3⟩
  have houtside_le :
      (T \ S.I2).card ≤ 2 := by
    calc
      (T \ S.I2).card ≤ ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card := Finset.card_le_card hcover
      _ ≤ (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by omega
      _ = 2 := by norm_num
  have hsplit : (T \ S.I2).card + (T ∩ S.I2).card = T.card := by
    simpa [Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I2
  have hinter_le : (T ∩ S.I2).card ≤ S.I2.card := Finset.card_le_card Finset.inter_subset_right
  have hTfour : 4 ≤ T.card := by
    show 4 ≤ (A.filter (fun q => dist S.MT.toMoserTriangle.v2 q = r)).card
    exact hTcard
  omega
theorem I3_card_ge_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    2 ≤ S.I3.card := by
  classical
  rcases S.k4_at_v3 with ⟨r, hrpos, hTcard⟩
  let T : Finset ℝ² := A.filter (fun x => dist S.triangle.v3 x = r)
  have hv3_not_mem_T : S.triangle.v3 ∉ T := by
    intro hv3T
    have hv3eq : dist S.triangle.v3 S.triangle.v3 = r := (Finset.mem_filter.mp hv3T).2
    have h0r : (0 : ℝ) = r := by simpa using hv3eq
    nlinarith only [hrpos, h0r]
  have hC1_one : (T ∩ S.CP.C1).card ≤ 1 := by
    apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v3_of_supportCap
      (A := A) (C := S.CP.C1) (M := S.triangle)
      S.hconv S.hnoncol S.CP.C1_subset
      (fun x hxA => (S.CP.arc_membership x hxA).1)
      S.CP.v2_mem_C1 S.CP.v3_mem_C1 S.Packet S.Packet.inner_at_v1
      (S := T ∩ S.CP.C1) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      simpa using (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
  have hC2_one : (T ∩ S.CP.C2).card ≤ 1 := by
    apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v2_of_supportCap
      (A := A) (C := S.CP.C2) (M := S.triangle2)
      S.hconv S.hnoncol S.CP.C2_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.1)
      S.CP.v3_mem_C2 S.CP.v1_mem_C2 S.packet2 S.packet2.inner_at_v1
      (S := T ∩ S.CP.C2) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
  have hcover :
      T \ S.I3 ⊆ (T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2) := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnotI3⟩
    have hxA : x ∈ A := (Finset.mem_filter.mp hxT).1
    by_cases hxv2 : x = S.triangle.v2
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv2] using S.CP.v2_mem_C1⟩
    by_cases hxv1 : x = S.triangle.v1
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv1] using S.CP.v1_mem_C2⟩
    by_cases hxv3 : x = S.triangle.v3
    · exact False.elim (hv3_not_mem_T (hxv3 ▸ hxT))
    have hxnonmoser : x ∉ S.triangle.verts := by
      simp [Problem97.MoserTriangle.verts, hxv1, hxv2, hxv3]
    have hxnotC3 : x ∉ S.CP.C3 := by
      intro hxC3
      have hxI3 : x ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hxv2, Finset.mem_erase.mpr ⟨hxv1, hxC3⟩⟩
      exact hxnotI3 hxI3
    have hone := S.CP.nonmoser_in_one x hxA hxnonmoser
    by_cases hxC1 : x ∈ S.CP.C1
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hxT, hxC1⟩
    · have hxC2 : x ∈ S.CP.C2 := by
        by_cases hxC2 : x ∈ S.CP.C2
        · exact hxC2
        · have : (0 : ℕ) = 1 := by
            simpa [hxC1, hxC2, hxnotC3] using hone
          omega
      apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxT, hxC2⟩
  have houtside_le :
      (T \ S.I3).card ≤ 2 := by
    calc
      (T \ S.I3).card ≤ ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card := Finset.card_le_card hcover
      _ ≤ (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by omega
      _ = 2 := by norm_num
  have hsplit : (T \ S.I3).card + (T ∩ S.I3).card = T.card := by
    simpa [Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I3
  have hinter_le : (T ∩ S.I3).card ≤ S.I3.card := Finset.card_le_card Finset.inter_subset_right
  have hTfour : 4 ≤ T.card := by
    show 4 ≤ (A.filter (fun q => dist S.MT.toMoserTriangle.v3 q = r)).card
    exact hTcard
  omega
theorem I1_card
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.I1.card + 2 = S.CP.C1.card := by
  classical
  obtain ⟨h12, h23, h13, _⟩ := S.hCirc
  have hv3 :
      S.MT.toMoserTriangle.v3 ∈ S.CP.C1.erase S.MT.toMoserTriangle.v2 := by
    exact Finset.mem_erase.mpr ⟨by intro h; exact h23 h.symm, S.CP.v3_mem_C1⟩
  have hC1erase :
      (S.CP.C1.erase S.MT.toMoserTriangle.v2).card = S.CP.C1.card - 1 :=
    Finset.card_erase_of_mem S.CP.v2_mem_C1
  have hI1 :
      S.I1.card = (S.CP.C1.erase S.MT.toMoserTriangle.v2).card - 1 := by
    unfold I1
    exact Finset.card_erase_of_mem hv3
  have hC1_ge_two : 2 ≤ S.CP.C1.card := by
    have hsubset :
        ({S.MT.toMoserTriangle.v2, S.MT.toMoserTriangle.v3} : Finset ℝ²) ⊆ S.CP.C1 := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact S.CP.v2_mem_C1
      · exact S.CP.v3_mem_C1
    have hcard_le := Finset.card_le_card hsubset
    simpa [h23] using hcard_le
  rw [hI1, hC1erase]
  omega
theorem I2_card
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.I2.card + 2 = S.CP.C2.card := by
  classical
  obtain ⟨h12, h23, h13, _⟩ := S.hCirc
  have hv1 :
      S.MT.toMoserTriangle.v1 ∈ S.CP.C2.erase S.MT.toMoserTriangle.v3 := by
    exact Finset.mem_erase.mpr ⟨h13, S.CP.v1_mem_C2⟩
  have hC2erase :
      (S.CP.C2.erase S.MT.toMoserTriangle.v3).card = S.CP.C2.card - 1 :=
    Finset.card_erase_of_mem S.CP.v3_mem_C2
  have hI2 :
      S.I2.card = (S.CP.C2.erase S.MT.toMoserTriangle.v3).card - 1 := by
    unfold I2
    exact Finset.card_erase_of_mem hv1
  have hC2_ge_two : 2 ≤ S.CP.C2.card := by
    have hsubset :
        ({S.MT.toMoserTriangle.v3, S.MT.toMoserTriangle.v1} : Finset ℝ²) ⊆ S.CP.C2 := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact S.CP.v3_mem_C2
      · exact S.CP.v1_mem_C2
    have h31 : S.MT.toMoserTriangle.v3 ≠ S.MT.toMoserTriangle.v1 := by
      intro h
      exact h13 h.symm
    have hpair :
        ({S.MT.toMoserTriangle.v3, S.MT.toMoserTriangle.v1} : Finset ℝ²).card = 2 := by
      simp [h31]
    have hcard_le := Finset.card_le_card hsubset
    rw [hpair] at hcard_le
    exact hcard_le
  rw [hI2, hC2erase]
  omega
theorem I3_card
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.I3.card + 2 = S.CP.C3.card := by
  classical
  obtain ⟨h12, h23, h13, _⟩ := S.hCirc
  have hv2 :
      S.MT.toMoserTriangle.v2 ∈ S.CP.C3.erase S.MT.toMoserTriangle.v1 := by
    exact Finset.mem_erase.mpr ⟨by intro h; exact h12 h.symm, S.CP.v2_mem_C3⟩
  have hC3erase :
      (S.CP.C3.erase S.MT.toMoserTriangle.v1).card = S.CP.C3.card - 1 :=
    Finset.card_erase_of_mem S.CP.v1_mem_C3
  have hI3 :
      S.I3.card = (S.CP.C3.erase S.MT.toMoserTriangle.v1).card - 1 := by
    unfold I3
    exact Finset.card_erase_of_mem hv2
  have hC3_ge_two : 2 ≤ S.CP.C3.card := by
    have hsubset :
        ({S.MT.toMoserTriangle.v1, S.MT.toMoserTriangle.v2} : Finset ℝ²) ⊆ S.CP.C3 := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact S.CP.v1_mem_C3
      · exact S.CP.v2_mem_C3
    have hcard_le := Finset.card_le_card hsubset
    simpa [h12] using hcard_le
  rw [hI3, hC3erase]
  omega
theorem cap1_card_ge_four_of_I1_card_ge_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (hI1 : 2 ≤ S.I1.card) :
    4 ≤ S.CP.C1.card := by
  have hcard := S.I1_card
  omega
theorem cap2_card_ge_four_of_I2_card_ge_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (hI2 : 2 ≤ S.I2.card) :
    4 ≤ S.CP.C2.card := by
  have hcard := S.I2_card
  omega
theorem cap3_card_ge_four_of_I3_card_ge_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (hI3 : 2 ≤ S.I3.card) :
    4 ≤ S.CP.C3.card := by
  have hcard := S.I3_card
  omega
theorem n4b_n5_exact_cap_vector_of_interior_lower_bounds
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hI1 : 2 ≤ S.I1.card) (hI2 : 2 ≤ S.I2.card) (hI3 : 2 ≤ S.I3.card) :
    S.CP.C1.card = 4 ∧ S.CP.C2.card = 4 ∧ S.CP.C3.card = 4
      ∧ S.I1.card = 2 ∧ S.I2.card = 2 ∧ S.I3.card = 2 := by
  have hC1_ge : 4 ≤ S.CP.C1.card := S.cap1_card_ge_four_of_I1_card_ge_two hI1
  have hC2_ge : 4 ≤ S.CP.C2.card := S.cap2_card_ge_four_of_I2_card_ge_two hI2
  have hC3_ge : 4 ≤ S.CP.C3.card := S.cap3_card_ge_four_of_I3_card_ge_two hI3
  have hsum := S.hcapSum12
  have hC1_eq : S.CP.C1.card = 4 := by
    omega
  have hC2_eq : S.CP.C2.card = 4 := by
    omega
  have hC3_eq : S.CP.C3.card = 4 := by
    omega
  have hI1_eq : S.I1.card = 2 := by
    have hcard := S.I1_card
    omega
  have hI2_eq : S.I2.card = 2 := by
    have hcard := S.I2_card
    omega
  have hI3_eq : S.I3.card = 2 := by
    have hcard := S.I3_card
    omega
  exact ⟨hC1_eq, hC2_eq, hC3_eq, hI1_eq, hI2_eq, hI3_eq⟩
theorem n5_forced_m44_of_interior_lower_bounds
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hI1 : 2 ≤ S.I1.card) (hI2 : 2 ≤ S.I2.card) (hI3 : 2 ≤ S.I3.card) :
    S.CP.C1.card = 4 ∧ S.CP.C2.card = 4 ∧ S.CP.C3.card = 4 := by
  rcases S.n4b_n5_exact_cap_vector_of_interior_lower_bounds hI1 hI2 hI3 with
    ⟨hC1, hC2, hC3, -, -, -⟩
  exact ⟨hC1, hC2, hC3⟩
theorem n5_forced_m44
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.CP.C1.card = 4 ∧ S.CP.C2.card = 4 ∧ S.CP.C3.card = 4 := by
  exact S.n5_forced_m44_of_interior_lower_bounds
    S.I1_card_ge_two S.I2_card_ge_two S.I3_card_ge_two
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit045



open scoped EuclideanGeometry InnerProductSpace

namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell

noncomputable def b3n9m051_coreSupport {A : Finset ℝ²}
    (S : FiniteEndpointShell A) : N4eCoreSupport S :=
  Classical.choice (Erdos9796FiniteNine.n4e_core S)

theorem b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 :=
  Problem97.dist_sq_coord x y
theorem b3n9m051_qEqE_f1_sinusoid (r δ ε t S : ℝ) (hS : S ^ 2 = 2 - 2 * Real.cos (δ - ε)) :
    ((((1 + r * Real.cos δ) + r * S * Real.cos t) - (1 + r * Real.cos (2 * δ - ε)))
          * ((1 + r * Real.cos δ) - 1)
        + (((r * Real.sin δ) + r * S * Real.sin t) - r * Real.sin (2 * δ - ε))
          * ((r * Real.sin δ) - 0))
      = r ^ 2 * S * (Real.cos (t - δ) + S / 2) := by
  have e1 :
      Real.cos (2 * δ - ε)
        = (2 * Real.cos δ ^ 2 - 1) * Real.cos ε + (2 * Real.sin δ * Real.cos δ) * Real.sin ε := by
    rw [show (2 * δ - ε) = 2 * δ + (-ε) by ring, Real.cos_add, Real.cos_two_mul,
        Real.sin_two_mul, Real.cos_neg, Real.sin_neg]; ring
  have e2 :
      Real.sin (2 * δ - ε)
        = (2 * Real.sin δ * Real.cos δ) * Real.cos ε - (2 * Real.cos δ ^ 2 - 1) * Real.sin ε := by
    rw [show (2 * δ - ε) = 2 * δ + (-ε) by ring, Real.sin_add, Real.cos_two_mul,
        Real.sin_two_mul, Real.cos_neg, Real.sin_neg]; ring
  have e3 : Real.cos (t - δ) = Real.cos t * Real.cos δ + Real.sin t * Real.sin δ :=
    Real.cos_sub t δ
  have hSe : S ^ 2 = 2 - 2 * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε) := by
    rw [hS, Real.cos_sub]
  have hp : Real.sin δ ^ 2 + Real.cos δ ^ 2 = 1 := Real.sin_sq_add_cos_sq δ
  rw [e1, e2, e3]
  linear_combination (-r ^ 2 * (2 * Real.cos δ * Real.cos ε - 1)) * hp + (-r ^ 2 / 2) * hSe
theorem b3n9m051_qEqE_f2_sinusoid (r δ ε t S : ℝ) :
    ((((1 + r * Real.cos δ) + r * S * Real.cos t) - (1 + r * Real.cos (2 * δ - ε)))
          * (1 + r * Real.cos δ)
        + (((r * Real.sin δ) + r * S * Real.sin t) - r * Real.sin (2 * δ - ε))
          * (r * Real.sin δ))
      = r * S * ((1 + r * Real.cos δ) * Real.cos t + r * Real.sin δ * Real.sin t)
        + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε) + Real.cos δ
               - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                  + (2 * Real.sin δ * Real.cos δ) * Real.sin ε)) := by
  have e1 :
      Real.cos (2 * δ - ε)
        = (2 * Real.cos δ ^ 2 - 1) * Real.cos ε + (2 * Real.sin δ * Real.cos δ) * Real.sin ε := by
    rw [show (2 * δ - ε) = 2 * δ + (-ε) by ring, Real.cos_add, Real.cos_two_mul,
        Real.sin_two_mul, Real.cos_neg, Real.sin_neg]; ring
  have e2 :
      Real.sin (2 * δ - ε)
        = (2 * Real.sin δ * Real.cos δ) * Real.cos ε - (2 * Real.cos δ ^ 2 - 1) * Real.sin ε := by
    rw [show (2 * δ - ε) = 2 * δ + (-ε) by ring, Real.sin_add, Real.cos_two_mul,
        Real.sin_two_mul, Real.cos_neg, Real.sin_neg]; ring
  have hp : Real.sin δ ^ 2 + Real.cos δ ^ 2 = 1 := Real.sin_sq_add_cos_sq δ
  rw [e1, e2]
  linear_combination (-r ^ 2 * (2 * Real.cos δ * Real.cos ε - 1)) * hp
theorem b3n9m051_qEqE_signblock_reduction (r δ ε t S : ℝ) (hr : 0 < r) (hS : 0 < S)
    (hS2 : S ^ 2 = 2 - 2 * Real.cos (δ - ε))
    (hUwxb : 0 ≤ (Real.cos (t - δ) + S / 2)
              * (S * Real.cos t + Real.cos δ - Real.cos (2 * δ - ε))) :
    0 ≤ (r ^ 2 * S * (Real.cos (t - δ) + S / 2))
        * (r * S * ((1 + r * Real.cos δ) * Real.cos t
              + r * Real.sin δ * Real.sin t)
           + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε)
                + Real.cos δ
                - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                   + (2 * Real.sin δ * Real.cos δ) * Real.sin ε))) := by
  have hcsub : Real.cos (t - δ)
      = Real.cos t * Real.cos δ + Real.sin t * Real.sin δ := Real.cos_sub t δ
  have he1 : Real.cos (2 * δ - ε)
      = (2 * Real.cos δ ^ 2 - 1) * Real.cos ε
        + (2 * Real.sin δ * Real.cos δ) * Real.sin ε := by
    rw [show (2 * δ - ε) = 2 * δ + (-ε) by ring, Real.cos_add, Real.cos_two_mul,
        Real.sin_two_mul, Real.cos_neg, Real.sin_neg]; ring
  have hcsd : Real.cos (δ - ε)
      = Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε := Real.cos_sub δ ε
  have hSe : S ^ 2 = 2 - 2 * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε) := by
    rw [hS2, hcsd]
  set U := Real.cos (t - δ) + S / 2 with hU
  have key : (r ^ 2 * S * U)
        * (r * S * ((1 + r * Real.cos δ) * Real.cos t
              + r * Real.sin δ * Real.sin t)
           + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε)
                + Real.cos δ
                - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                   + (2 * Real.sin δ * Real.cos δ) * Real.sin ε)))
      = r ^ 3 * S * (r * S * U ^ 2
          + U * (S * Real.cos t + Real.cos δ - Real.cos (2 * δ - ε))) := by
    rw [he1, hU, hcsub]
    linear_combination
      (-(S * r ^ 4 * (Real.cos t * Real.cos δ + Real.sin t * Real.sin δ + S / 2)) / 2) * hSe
  rw [show (r ^ 2 * S * (Real.cos (t - δ) + S / 2)) = (r ^ 2 * S * U) by rw [hU], key]
  have h3 : 0 ≤ r * S * U ^ 2
        + U * (S * Real.cos t + Real.cos δ - Real.cos (2 * δ - ε)) := by
    have h2 : 0 ≤ r * S * U ^ 2 := by positivity
    have hb : 0 ≤ U * (S * Real.cos t + Real.cos δ - Real.cos (2 * δ - ε)) := hUwxb
    linarith
  exact mul_nonneg (by positivity) h3
namespace QEqEOneCosine
lemma b3n9m051_cs_bound (ct st nx ny : ℝ) (hpt : ct ^ 2 + st ^ 2 = 1)
    (hn1 : nx ^ 2 + ny ^ 2 = 1) : ct * nx + st * ny ≤ 1 := by
  have h : 0 ≤ (ct - nx) ^ 2 + (st - ny) ^ 2 := by positivity
  nlinarith only [hpt, hn1, h]
lemma b3n9m051_cd_nonneg (r cd sd ce se : ℝ) (hr : 0 < r)
    (hpd : cd ^ 2 + sd ^ 2 = 1) (hpe : ce ^ 2 + se ^ 2 = 1)
    (hsd : 0 < sd) (hse : 0 < se) (hce : ce < -(r / 2)) (hcd : -(r / 2) < cd)
    (hs2de' : 2 * sd * cd * ce - (2 * cd ^ 2 - 1) * se < 0)
    (hc2de' : (2 * cd ^ 2 - 1) * ce + 2 * sd * cd * se < -(r / 2)) : 0 ≤ cd := by
  nlinarith only [hpe, hr, hcd, hc2de', hse, hs2de', hce, hpd, hsd, mul_pos hsd hse, sq_nonneg sd, mul_pos hr hse, mul_pos hsd hsd]
lemma b3n9m051_sz_eq (S Z cd sd ce se : ℝ) (hS : 0 < S) (hZ : 0 ≤ Z)
    (hZsq : Z ^ 2 = 1 - S ^ 2 / 4) (hS2 : S ^ 2 = 2 - 2 * (cd * ce + sd * se))
    (hpd : cd ^ 2 + sd ^ 2 = 1) (hpe : ce ^ 2 + se ^ 2 = 1)
    (hsed : 0 ≤ se * cd - ce * sd) : S * Z = se * cd - ce * sd := by
  have hSZsq : (S * Z) ^ 2 = (se * cd - ce * sd) ^ 2 := by
    have hexp : (S * Z) ^ 2 = S ^ 2 * (Z ^ 2) := by ring
    rw [hexp, hZsq]
    linear_combination (-(S ^ 2 - 2 * cd * ce - 2 * sd * se - 2) / 4) * hS2
      + (-ce ^ 2 - se ^ 2) * hpd + (-1 : ℝ) * hpe
  have hSZnn : 0 ≤ S * Z := mul_nonneg (le_of_lt hS) hZ
  nlinarith only [hSZsq, hSZnn, hsed, sq_nonneg (S * Z - (se * cd - ce * sd))]
lemma b3n9m051_E_nonneg (S Z cd sd ce se st : ℝ)
    (hsd : 0 < sd) (hse : 0 < se) (hcd0 : 0 ≤ cd) (hZ : 0 ≤ Z) (hS : 0 < S)
    (hst_le : S * st + sd ≤ 0) (hSZ : S * Z = se * cd - ce * sd)
    (hS2 : S ^ 2 = 2 - 2 * (cd * ce + sd * se))
    (hpd : cd ^ 2 + sd ^ 2 = 1) (hpe : ce ^ 2 + se ^ 2 = 1)
    (hs2de' : 2 * sd * cd * ce - (2 * cd ^ 2 - 1) * se < 0) :
    0 ≤ cd ^ 2 + st ^ 2 - S ^ 2 / 4 - 2 * Z * cd * st := by
  have hS2pos : 0 < S ^ 2 := by positivity
  have hT : 0 ≤ se * (2 * sd - (2 * sd * cd * ce - (2 * cd ^ 2 - 1) * se)) :=
    mul_nonneg (le_of_lt hse) (by linarith)
  set EsmaxS2 := -S ^ 4 / 4 + S ^ 2 * cd ^ 2 + 2 * S * Z * cd * sd + sd ^ 2 with hEs
  have hEsT : EsmaxS2 = se * (2 * sd - (2 * sd * cd * ce - (2 * cd ^ 2 - 1) * se)) := by
    rw [hEs]
    linear_combination (2 * cd * sd) * hSZ
      + (-(S ^ 2 - 4 * cd ^ 2 - 2 * cd * ce - 2 * sd * se + 2) / 4) * hS2
      + (-2 * cd * ce - ce ^ 2 - 2 * se ^ 2 + 2) * hpd + ((sd - 1) * (sd + 1)) * hpe
  have hEsmax : 0 ≤ EsmaxS2 := hEsT ▸ hT
  have hSZcd : 0 ≤ 2 * S * Z * cd := by positivity
  have hfac2 : S * st - sd - 2 * S * Z * cd ≤ 0 := by nlinarith only [hsd, hst_le, hSZcd]
  have hprod : 0 ≤ (S * st + sd) * (S * st - sd - 2 * S * Z * cd) := by
    have h := mul_nonneg (neg_nonneg.mpr hst_le) (neg_nonneg.mpr hfac2); nlinarith only [h]
  have hES2 : (cd ^ 2 + st ^ 2 - S ^ 2 / 4 - 2 * Z * cd * st) * S ^ 2
      = EsmaxS2 + (S * st + sd) * (S * st - sd - 2 * S * Z * cd) := by rw [hEs]; ring
  nlinarith only [hEs, hEsT, hprod, hsd, hse, hs2de', hES2, hEsmax, hS2pos]
lemma b3n9m051_one_cosine (S Z cd ct st : ℝ)
    (hS : 0 < S) (hZ : 0 ≤ Z) (hZsq : Z ^ 2 = 1 - S ^ 2 / 4)
    (hpt : ct ^ 2 + st ^ 2 = 1) (hcd0 : 0 ≤ cd) (hstneg : st < 0)
    (hE : 0 ≤ cd ^ 2 + st ^ 2 - S ^ 2 / 4 - 2 * Z * cd * st) :
    -(S / 2) * ct + Z * st ≤ cd := by
  have hZst : Z * st ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hZ (le_of_lt hstneg)
  have hrhs : 0 ≤ cd - Z * st := by linarith
  have hsq : (S / 2 * |ct|) ^ 2 ≤ (cd - Z * st) ^ 2 := by
    have hct2 : ct ^ 2 = 1 - st ^ 2 := by linarith [hpt]
    have heq : (S / 2 * |ct|) ^ 2 = S ^ 2 / 4 * (1 - st ^ 2) := by rw [mul_pow, sq_abs, hct2]; ring
    rw [heq]; nlinarith only [hE, hZsq]
  have habs : S / 2 * |ct| ≤ cd - Z * st := by
    have h1 : (0:ℝ) ≤ S / 2 * |ct| := by positivity
    nlinarith only [hsq, hcd0, hZst, h1, hrhs]
  have hnct : -ct ≤ |ct| := neg_le_abs ct
  have hmul : (S / 2) * (-ct) ≤ S / 2 * |ct| := mul_le_mul_of_nonneg_left hnct (by positivity)
  nlinarith only [habs, hmul]
end QEqEOneCosine
set_option maxHeartbeats 400000 in
theorem qEqE_oneCosine_crux_of_signs (r δ ε t S : ℝ)
    (hr : 0 < r) (hS : 0 < S)
    (hS2eq : S ^ 2 = 2 - 2 * Real.cos (δ - ε))
    (hsd : 0 < Real.sin δ) (hse : 0 < Real.sin ε)
    (hcd0 : 0 ≤ Real.cos δ)
    (hsed : 0 ≤ Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ)
    (hs2de : Real.sin (2 * δ - ε) < 0)
    (hlower : r * Real.sin δ + r * S * Real.sin t < 0) :
    0 ≤ (Real.cos (t - δ) + S / 2)
        * (S * Real.cos t + Real.cos δ - Real.cos (2 * δ - ε)) := by
  set cd := Real.cos δ with hcd_def
  set sd := Real.sin δ with hsd_def
  set ce := Real.cos ε with hce_def
  set se := Real.sin ε with hse_def
  set ct := Real.cos t with hct_def
  set st := Real.sin t with hst_def
  have hpd : cd ^ 2 + sd ^ 2 = 1 := by rw [hcd_def, hsd_def, add_comm]; exact Real.sin_sq_add_cos_sq δ
  have hpe : ce ^ 2 + se ^ 2 = 1 := by rw [hce_def, hse_def, add_comm]; exact Real.sin_sq_add_cos_sq ε
  have hpt : ct ^ 2 + st ^ 2 = 1 := by rw [hct_def, hst_def, add_comm]; exact Real.sin_sq_add_cos_sq t
  have hc2de_eq : Real.cos (2 * δ - ε) = (2 * cd ^ 2 - 1) * ce + 2 * sd * cd * se := by
    rw [hcd_def, hce_def, hsd_def, hse_def,
        show (2 * δ - ε) = 2 * δ + (-ε) by ring, Real.cos_add, Real.cos_two_mul,
        Real.sin_two_mul, Real.cos_neg, Real.sin_neg]; ring
  have hs2de_eq : Real.sin (2 * δ - ε) = 2 * sd * cd * ce - (2 * cd ^ 2 - 1) * se := by
    rw [hcd_def, hce_def, hsd_def, hse_def,
        show (2 * δ - ε) = 2 * δ + (-ε) by ring, Real.sin_add, Real.cos_two_mul,
        Real.sin_two_mul, Real.cos_neg, Real.sin_neg]; ring
  have hcde_eq : Real.cos (δ - ε) = cd * ce + sd * se := by
    rw [hcd_def, hce_def, hsd_def, hse_def, Real.cos_sub]
  have hctd_eq : Real.cos (t - δ) = ct * cd + st * sd := by
    rw [hct_def, hcd_def, hst_def, hsd_def, Real.cos_sub]
  have hS2 : S ^ 2 = 2 - 2 * (cd * ce + sd * se) := by rw [hS2eq, hcde_eq]
  have hs2de' : 2 * sd * cd * ce - (2 * cd ^ 2 - 1) * se < 0 := by rw [← hs2de_eq]; exact hs2de
  have hcd0_cd : 0 ≤ cd := by simpa [hcd_def] using hcd0
  have hsed_cd : 0 ≤ se * cd - ce * sd := by
    simpa [hse_def, hcd_def, hce_def, hsd_def] using hsed
  have hcde_gt : -1 < cd * ce + sd * se := by
    nlinarith only [hpd, hpe, hsd, hse, mul_pos hsd hse, sq_nonneg (cd - ce), sq_nonneg (sd - se)]
  have h14 : (0:ℝ) ≤ 1 - S ^ 2 / 4 := by rw [hS2]; linarith
  set Z := Real.sqrt (1 - S ^ 2 / 4) with hZ_def
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hZsq : Z ^ 2 = 1 - S ^ 2 / 4 := by rw [hZ_def, Real.sq_sqrt h14]
  have hSZ : S * Z = se * cd - ce * sd :=
    QEqEOneCosine.b3n9m051_sz_eq S Z cd sd ce se hS hZ hZsq hS2 hpd hpe hsed_cd
  have hst_le : S * st + sd ≤ 0 := by nlinarith only [hlower, hr]
  have hstneg : st < 0 := by nlinarith only [hS, hsd, hst_le]
  set nx := -(S/2) * cd + Z * sd with hnx_def
  set ny := -(S/2) * sd - Z * cd with hny_def
  set ctb := -(S/2) * ct + Z * st with hctb_def
  have hn1 : nx ^ 2 + ny ^ 2 = 1 := by
    rw [hnx_def, hny_def]; linear_combination ((S ^ 2 + 4 * Z ^ 2) / 4) * hpd + hZsq
  have hwxbA : S * ct + cd - Real.cos (2 * δ - ε) = S * (ct - nx) := by
    rw [hc2de_eq, hnx_def]; linear_combination (-ce) * hpd + sd * hSZ + (-cd / 2) * hS2
  have hU_def : Real.cos (t - δ) + S / 2 = ct * cd + st * sd + S / 2 := by rw [hctd_eq]
  have hwxbB : (ct * cd + st * sd + S / 2) * (S * (ct - nx))
      = S * (1 - (ct * nx + st * ny)) * (cd - ctb) := by
    rw [hnx_def, hny_def, hctb_def]
    linear_combination (-S * Z * st) * hpd
      + (-S * (S ^ 2 * cd - 2 * S * Z * sd - 4 * cd) / 4) * hpt
      + (S * st * (cd * st - ct * sd)) * hZsq
  have hmaster : (Real.cos (t - δ) + S / 2) * (S * Real.cos t + Real.cos δ - Real.cos (2 * δ - ε))
      = S * (1 - (ct * nx + st * ny)) * (cd - ctb) := by
    rw [hU_def, ← hct_def, ← hcd_def, hwxbA, hwxbB]
  rw [hmaster]
  have hmn : ct * nx + st * ny ≤ 1 := QEqEOneCosine.b3n9m051_cs_bound ct st nx ny hpt hn1
  have hfac1 : 0 ≤ S * (1 - (ct * nx + st * ny)) := mul_nonneg (le_of_lt hS) (by linarith [hmn])
  have hE : 0 ≤ cd ^ 2 + st ^ 2 - S ^ 2 / 4 - 2 * Z * cd * st :=
    QEqEOneCosine.b3n9m051_E_nonneg S Z cd sd ce se st hsd hse hcd0_cd hZ hS hst_le hSZ hS2 hpd hpe hs2de'
  have hone : ctb ≤ cd := by
    rw [hctb_def]; exact QEqEOneCosine.b3n9m051_one_cosine S Z cd ct st hS hZ hZsq hpt hcd0_cd hstneg hE
  have hfac3 : 0 ≤ cd - ctb := by linarith [hone]
  exact mul_nonneg hfac1 hfac3
set_option maxHeartbeats 400000 in
theorem qEqE_oneCosine_crux (r δ ε t S : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hS : 0 < S)
    (hS2eq : S ^ 2 = 2 - 2 * Real.cos (δ - ε))
    (hsd : 0 < Real.sin δ) (hcd : -(r / 2) < Real.cos δ)
    (hse : 0 < Real.sin ε) (hce : Real.cos ε < -(r / 2))
    (hs2de : Real.sin (2 * δ - ε) < 0) (hc2de : Real.cos (2 * δ - ε) < -(r / 2))
    (hlower : r * Real.sin δ + r * S * Real.sin t < 0) :
    0 ≤ (Real.cos (t - δ) + S / 2)
        * (S * Real.cos t + Real.cos δ - Real.cos (2 * δ - ε)) := by
  have hpd : Real.cos δ ^ 2 + Real.sin δ ^ 2 = 1 := by
    rw [add_comm]
    exact Real.sin_sq_add_cos_sq δ
  have hpe : Real.cos ε ^ 2 + Real.sin ε ^ 2 = 1 := by
    rw [add_comm]
    exact Real.sin_sq_add_cos_sq ε
  have hc2de_eq :
      Real.cos (2 * δ - ε) =
        (2 * Real.cos δ ^ 2 - 1) * Real.cos ε
          + 2 * Real.sin δ * Real.cos δ * Real.sin ε := by
    rw [show (2 * δ - ε) = 2 * δ + (-ε) by ring, Real.cos_add,
      Real.cos_two_mul, Real.sin_two_mul, Real.cos_neg, Real.sin_neg]
    ring
  have hs2de_eq :
      Real.sin (2 * δ - ε) =
        2 * Real.sin δ * Real.cos δ * Real.cos ε
          - (2 * Real.cos δ ^ 2 - 1) * Real.sin ε := by
    rw [show (2 * δ - ε) = 2 * δ + (-ε) by ring, Real.sin_add,
      Real.cos_two_mul, Real.sin_two_mul, Real.cos_neg, Real.sin_neg]
    ring
  have hs2de' :
      2 * Real.sin δ * Real.cos δ * Real.cos ε
          - (2 * Real.cos δ ^ 2 - 1) * Real.sin ε < 0 := by
    rw [← hs2de_eq]
    exact hs2de
  have hc2de' :
      (2 * Real.cos δ ^ 2 - 1) * Real.cos ε
          + 2 * Real.sin δ * Real.cos δ * Real.sin ε < -(r / 2) := by
    rw [← hc2de_eq]
    exact hc2de
  have hcd0 : 0 ≤ Real.cos δ :=
    QEqEOneCosine.b3n9m051_cd_nonneg r (Real.cos δ) (Real.sin δ) (Real.cos ε) (Real.sin ε)
      hr hpd hpe hsd hse hce hcd hs2de' hc2de'
  have hsed : 0 ≤ Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ := by
    have h1 : 0 ≤ Real.sin ε * Real.cos δ := mul_nonneg (le_of_lt hse) hcd0
    have h2 : Real.cos ε * Real.sin δ < 0 := mul_neg_of_neg_of_pos (by linarith) hsd
    linarith
  exact qEqE_oneCosine_crux_of_signs r δ ε t S hr hS hS2eq hsd hse hcd0 hsed hs2de hlower
set_option maxHeartbeats 400000 in
theorem qEqE_lowerArc_sameSign (r δ ε t S : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hS : 0 < S)
    (hS2eq : S ^ 2 = 2 - 2 * Real.cos (δ - ε))
    (hsd : 0 < Real.sin δ) (hcd : -(r / 2) < Real.cos δ)
    (hse : 0 < Real.sin ε) (hce : Real.cos ε < -(r / 2))
    (hs2de : Real.sin (2 * δ - ε) < 0) (hc2de : Real.cos (2 * δ - ε) < -(r / 2))
    (hlower : r * Real.sin δ + r * S * Real.sin t < 0) :
    0 ≤ (r ^ 2 * S * (Real.cos (t - δ) + S / 2))
        * (r * S * ((1 + r * Real.cos δ) * Real.cos t
              + r * Real.sin δ * Real.sin t)
           + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε)
                + Real.cos δ
                - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                   + (2 * Real.sin δ * Real.cos δ) * Real.sin ε))) :=
  b3n9m051_qEqE_signblock_reduction r δ ε t S hr hS hS2eq
    (qEqE_oneCosine_crux r δ ε t S hr hr1 hS hS2eq hsd hcd hse hce hs2de hc2de hlower)
theorem qEqE_lowerArc_sameSign_flipped_of_signs (r δ ε t S : ℝ)
    (hr : 0 < r) (hS : 0 < S)
    (hS2eq : S ^ 2 = 2 - 2 * Real.cos (δ - ε))
    (hsd : 0 < Real.sin δ) (hse : 0 < Real.sin ε)
    (hcd0 : 0 ≤ Real.cos δ)
    (hsed : 0 ≤ Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ)
    (hs2de : Real.sin (2 * δ - ε) < 0)
    (hlower : r * Real.sin δ + r * S * Real.sin t < 0) :
    0 ≤ (r ^ 2 * S * (Real.cos (t - δ) + S / 2))
        * (r * S * ((1 + r * Real.cos δ) * Real.cos t
              + r * Real.sin δ * Real.sin t)
           + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε)
                + Real.cos δ
                - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                   + (2 * Real.sin δ * Real.cos δ) * Real.sin ε))) :=
  b3n9m051_qEqE_signblock_reduction r δ ε t S hr hS hS2eq
    (qEqE_oneCosine_crux_of_signs r δ ε t S hr hS hS2eq hsd hse hcd0 hsed hs2de hlower)
theorem b3n9m051_qEqE_noWrap_of_c2Side (r δ ε : ℝ)
    (hr : 0 < r) (hδπ : δ ≤ Real.pi) (hε0 : 0 ≤ ε)
    (hsd : 0 < Real.sin δ) (hse : 0 < Real.sin ε)
    (hcd : -(r / 2) < Real.cos δ)
    (hs2de : Real.sin (2 * δ - ε) < 0)
    (hside :
      Real.sin δ - Real.sin ε
        - r * (Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ) ≤ 0) :
    2 * δ < ε := by
  by_contra hnot
  push_neg at hnot
  set w : ℝ := 2 * δ - ε with hw_def
  have hw_nonneg : 0 ≤ w := by
    rw [hw_def]
    linarith
  have hδ_lt_pi : δ < Real.pi := by
    rcases lt_or_eq_of_le hδπ with h | h
    · exact h
    · exfalso
      rw [h, Real.sin_pi] at hsd
      exact lt_irrefl _ hsd
  have hπ_lt_w : Real.pi < w := by
    by_contra hnotπ
    push_neg at hnotπ
    have hsin_nonneg : 0 ≤ Real.sin w :=
      Real.sin_nonneg_of_nonneg_of_le_pi hw_nonneg hnotπ
    rw [hw_def] at hsin_nonneg
    exact (not_le_of_gt hs2de) hsin_nonneg
  have hε_lt_δ : ε < δ := by
    rw [hw_def] at hπ_lt_w
    linarith [hδ_lt_pi]
  have hε_pos : 0 < ε := by
    rcases lt_or_eq_of_le hε0 with h | h
    · exact h
    · exfalso
      rw [← h, Real.sin_zero] at hse
      exact lt_irrefl _ hse
  set u : ℝ := δ - ε with hu_def
  have hu_pos : 0 < u := by
    rw [hu_def]
    linarith
  have hu_lt_pi : u < Real.pi := by
    rw [hu_def]
    linarith [hδπ, hε_pos]
  have hsin_u_pos : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu_pos hu_lt_pi
  have hsd_nonneg : 0 ≤ Real.sin δ := le_of_lt hsd
  have hone_minus_cos_nonneg : 0 ≤ 1 - Real.cos u := by
    nlinarith only [Real.cos_le_one u]
  have hr_cos_pos : 0 < r + Real.cos δ := by
    linarith
  have hpos :
      0 < Real.sin δ * (1 - Real.cos u) + (r + Real.cos δ) * Real.sin u := by
    have hfirst : 0 ≤ Real.sin δ * (1 - Real.cos u) :=
      mul_nonneg hsd_nonneg hone_minus_cos_nonneg
    have hsecond : 0 < (r + Real.cos δ) * Real.sin u :=
      mul_pos hr_cos_pos hsin_u_pos
    linarith
  have hrewrite :
      Real.sin δ - Real.sin ε
          - r * (Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ)
        = Real.sin δ * (1 - Real.cos u) + (r + Real.cos δ) * Real.sin u := by
    rw [show Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ =
        Real.sin (ε - δ) by rw [Real.sin_sub]]
    rw [show ε - δ = -u by rw [hu_def]; ring, Real.sin_neg]
    rw [show ε = δ - u by rw [hu_def]; ring, Real.sin_sub]
    ring
  rw [hrewrite] at hside
  linarith
theorem qEqE_lowerArc_sameSign_flipped_of_noWrap (r δ ε t S : ℝ)
    (hr : 0 < r) (hS : 0 < S)
    (hS2eq : S ^ 2 = 2 - 2 * Real.cos (δ - ε))
    (hsd : 0 < Real.sin δ) (hse : 0 < Real.sin ε)
    (hδ0 : 0 ≤ δ) (hεπ : ε ≤ Real.pi)
    (h2δε : 2 * δ < ε)
    (hs2de : Real.sin (2 * δ - ε) < 0)
    (hlower : r * Real.sin δ + r * S * Real.sin t < 0) :
    0 ≤ (r ^ 2 * S * (Real.cos (t - δ) + S / 2))
        * (r * S * ((1 + r * Real.cos δ) * Real.cos t
              + r * Real.sin δ * Real.sin t)
           + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε)
                + Real.cos δ
                - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                   + (2 * Real.sin δ * Real.cos δ) * Real.sin ε))) := by
  have hδlt : δ < Real.pi / 2 := by
    nlinarith only [hεπ, h2δε]
  have hcd0 : 0 ≤ Real.cos δ := by
    exact le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδlt⟩)
  have hsed : 0 ≤ Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ := by
    have hdiff_nonneg : 0 ≤ ε - δ := by
      nlinarith only [hδ0, h2δε]
    have hdiff_le_pi : ε - δ ≤ Real.pi := by
      linarith [hεπ, hδ0]
    have hsin : 0 ≤ Real.sin (ε - δ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hdiff_nonneg hdiff_le_pi
    rwa [Real.sin_sub] at hsin
  exact qEqE_lowerArc_sameSign_flipped_of_signs r δ ε t S hr hS hS2eq hsd hse
    hcd0 hsed hs2de hlower
theorem qEqE_lowerArc_sameSign_flipped_of_c2Side (r δ ε t S : ℝ)
    (hr : 0 < r) (hS : 0 < S)
    (hS2eq : S ^ 2 = 2 - 2 * Real.cos (δ - ε))
    (hsd : 0 < Real.sin δ) (hcd : -(r / 2) < Real.cos δ)
    (hse : 0 < Real.sin ε)
    (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi)
    (hε0 : 0 ≤ ε) (hεπ : ε ≤ Real.pi)
    (hs2de : Real.sin (2 * δ - ε) < 0)
    (hside :
      Real.sin δ - Real.sin ε
        - r * (Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ) ≤ 0)
    (hlower : r * Real.sin δ + r * S * Real.sin t < 0) :
    0 ≤ (r ^ 2 * S * (Real.cos (t - δ) + S / 2))
        * (r * S * ((1 + r * Real.cos δ) * Real.cos t
              + r * Real.sin δ * Real.sin t)
           + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε)
                + Real.cos δ
                - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                   + (2 * Real.sin δ * Real.cos δ) * Real.sin ε))) := by
  have h2δε : 2 * δ < ε :=
    b3n9m051_qEqE_noWrap_of_c2Side r δ ε hr hδπ hε0 hsd hse hcd hs2de hside
  exact qEqE_lowerArc_sameSign_flipped_of_noWrap r δ ε t S hr hS hS2eq hsd hse
    hδ0 hεπ h2δε hs2de hlower

theorem b3n9m051_signedArea2_baseChord_vec2 (p : ℝ²) :
    signedArea2 p (Problem97.CGN.vec2 (-1) 0) (Problem97.CGN.vec2 1 0) = 2 * p 1 := by
  simp [Problem97.signedArea2, Problem97.CGN.vec2, EuclideanSpace.single_apply]
  ring
noncomputable def b3n9m051_similarityTransportComp
    {T1 T2 : ℝ² → ℝ²}
    (tau1 : Problem97.CGN.SimilarityTransportData T1)
    (tau2 : Problem97.CGN.SimilarityTransportData T2) :
    Problem97.CGN.SimilarityTransportData (fun x => T2 (T1 x)) := by
  classical
  refine
    { scale := tau2.scale * tau1.scale
      scale_pos := mul_pos tau2.scale_pos tau1.scale_pos
      dist_image := ?_
      dist_eq_iff := ?_
      convexHull_mem_iff := ?_
      orientation := tau2.orientation * tau1.orientation
      orientation_sq := ?_
      halfplane_sign := ?_ }
  · intro a b
    rw [tau2.dist_image, tau1.dist_image]
    ring
  · intro a b c
    constructor
    · intro h
      exact (tau1.dist_eq_iff a b c).1 ((tau2.dist_eq_iff (T1 a) (T1 b) (T1 c)).1 h)
    · intro h
      exact (tau2.dist_eq_iff (T1 a) (T1 b) (T1 c)).2 ((tau1.dist_eq_iff a b c).2 h)
  · intro S a
    have himage :
        (fun x => T2 (T1 x)) '' S = T2 '' (T1 '' S) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hxS, rfl⟩
        exact ⟨T1 x, ⟨x, hxS, rfl⟩, rfl⟩
      · intro hy
        rcases hy with ⟨z, ⟨x, hxS, rfl⟩, rfl⟩
        exact ⟨x, hxS, rfl⟩
    rw [himage]
    exact Iff.trans
      (tau2.convexHull_mem_iff (S := T1 '' S) (a := T1 a))
      (tau1.convexHull_mem_iff (S := S) (a := a))
  · have h1 := tau2.orientation_sq
    have h2 := tau1.orientation_sq
    ring_nf
    nlinarith only [h1, h2]
  · intro a b c
    rw [tau2.halfplane_sign, tau1.halfplane_sign]
    ring
noncomputable def b3n9m051_halfShift (p : ℝ²) : ℝ² :=
  Problem97.CGN.vec2 ((p 0 + 1) / 2) (p 1 / 2)
theorem b3n9m051_halfShift_injective : Function.Injective b3n9m051_halfShift := by
  intro p q hpq
  ext i <;> fin_cases i
  · have h := congrArg (fun z : ℝ² => z 0) hpq
    simpa [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply] using h
  · have h := congrArg (fun z : ℝ² => z 1) hpq
    simpa [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply] using h
noncomputable def b3n9m051_halfShiftSimilarityTransportData :
    Problem97.CGN.SimilarityTransportData b3n9m051_halfShift := by
  classical
  let F : ℝ² →ₗ[ℝ] ℝ² := (1 / 2 : ℝ) • LinearMap.id
  let c : ℝ² := Problem97.CGN.vec2 ((1 : ℝ) / 2) 0
  let Taff : ℝ² →ᵃ[ℝ] ℝ² := AffineMap.mk' b3n9m051_halfShift F c (by
    intro p
    ext i <;> fin_cases i <;>
      simp [b3n9m051_halfShift, F, c, Problem97.CGN.vec2, EuclideanSpace.single_apply, Pi.add_apply]
    · ring
    · ring
    )
  have hdist0 : ∀ a b : ℝ², dist (b3n9m051_halfShift a) (b3n9m051_halfShift b) = ((1 : ℝ) / 2) * dist a b := by
    intro a b
    have hcoord :
        b3n9m051_halfShift a - b3n9m051_halfShift b =
          (1 / 2 : ℝ) • (a - b) := by
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply, sub_eq_add_neg]
        <;> ring
    rw [dist_eq_norm, hcoord, norm_smul, Real.norm_of_nonneg (by positivity), dist_eq_norm]
  refine
    { scale := (1 : ℝ) / 2
      scale_pos := by positivity
      dist_image := ?_
      dist_eq_iff := ?_
      convexHull_mem_iff := ?_
      orientation := 1
      orientation_sq := by norm_num
      halfplane_sign := ?_ }
  · intro a b
    exact hdist0 a b
  · intro a b c
    constructor
    · intro h
      rw [hdist0 a b, hdist0 a c] at h
      nlinarith only [h]
    · intro h
      rw [hdist0 a b, hdist0 a c]
      nlinarith only [h]
  · intro S a
    have hmap : b3n9m051_halfShift '' convexHull ℝ S = convexHull ℝ (b3n9m051_halfShift '' S) := by
      simpa [Taff] using (AffineMap.image_convexHull Taff S)
    constructor
    · intro ha
      rw [← hmap] at ha
      rcases ha with ⟨b, hb, hTb⟩
      have hba : b = a := b3n9m051_halfShift_injective hTb
      simpa [hba] using hb
    · intro ha
      simpa [hmap] using (show b3n9m051_halfShift a ∈ b3n9m051_halfShift '' convexHull ℝ S from ⟨a, ha, rfl⟩)
  · intro a b c
    unfold b3n9m051_halfShift
    simp [Problem97.signedArea2, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    ring
noncomputable def b3n9m051_flipY (p : ℝ²) : ℝ² :=
  Problem97.CGN.vec2 (p 0) (-p 1)
theorem b3n9m051_flipY_injective : Function.Injective b3n9m051_flipY := by
  intro p q hpq
  ext i <;> fin_cases i
  · have h := congrArg (fun z : ℝ² => z 0) hpq
    simpa [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply] using h
  · have h := congrArg (fun z : ℝ² => z 1) hpq
    simpa [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply] using h
noncomputable def b3n9m051_flipYSimilarityTransportData :
    Problem97.CGN.SimilarityTransportData b3n9m051_flipY := by
  classical
  let F : ℝ² →ₗ[ℝ] ℝ² :=
    { toFun := b3n9m051_flipY
      map_add' := by
        intro x y
        ext i <;> fin_cases i <;>
          simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
        · ring
      map_smul' := by
        intro r x
        ext i <;> fin_cases i <;>
          simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      }
  let Taff : ℝ² →ᵃ[ℝ] ℝ² := AffineMap.mk' b3n9m051_flipY F 0 (by
    intro p
    ext i <;> fin_cases i <;>
      simp [b3n9m051_flipY, F, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    )
  have hdist0 : ∀ a b : ℝ², dist (b3n9m051_flipY a) (b3n9m051_flipY b) = dist a b := by
    intro a b
    have hsq :
        ‖b3n9m051_flipY a - b3n9m051_flipY b‖ ^ 2 = ‖a - b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply, Fin.sum_univ_two, sq_abs,
        Real.norm_eq_abs, PiLp.sub_apply]
      ring
    have hnonneg1 : 0 ≤ ‖b3n9m051_flipY a - b3n9m051_flipY b‖ := norm_nonneg _
    have hnonneg2 : 0 ≤ ‖a - b‖ := norm_nonneg _
    rw [dist_eq_norm, dist_eq_norm]
    nlinarith only [hsq, hnonneg1, hnonneg2]
  refine
    { scale := 1
      scale_pos := by norm_num
      dist_image := ?_
      dist_eq_iff := ?_
      convexHull_mem_iff := ?_
      orientation := -1
      orientation_sq := by norm_num
      halfplane_sign := ?_ }
  · intro a b
    simpa using hdist0 a b
  · intro a b c
    simpa [hdist0 a b, hdist0 a c]
  · intro S a
    have hmap : b3n9m051_flipY '' convexHull ℝ S = convexHull ℝ (b3n9m051_flipY '' S) := by
      simpa [Taff] using (AffineMap.image_convexHull Taff S)
    constructor
    · intro ha
      rw [← hmap] at ha
      rcases ha with ⟨b, hb, hTb⟩
      have hba : b = a := b3n9m051_flipY_injective hTb
      simpa [hba] using hb
    · intro ha
      simpa [hmap] using (show b3n9m051_flipY a ∈ b3n9m051_flipY '' convexHull ℝ S from ⟨a, ha, rfl⟩)
  · intro a b c
    unfold b3n9m051_flipY
    simp [Problem97.signedArea2, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    ring
theorem b3n9m051_exists_base_transportData
    (q1 q2 : ℝ²) (hqne : q1 ≠ q2) :
    ∃ T0, ∃ tau0 : Problem97.CGN.SimilarityTransportData T0,
      T0 q1 = Problem97.CGN.vec2 (-1) 0 ∧
      T0 q2 = Problem97.CGN.vec2 1 0 := by
  classical
  let A2 : Finset ℝ² := ({q1, q2} : Finset ℝ²)
  let L2 : Problem97.CGN.OrderedCap 2 :=
    { points := ![q1, q2]
      injective := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          exact hqne hij
        · exfalso
          exact hqne hij.symm
        · rfl }
  let P2 : Problem97.CGN.MecCapPacket A2 L2 :=
    { hm := by decide
      center := midpoint ℝ q1 q2
      radius := dist q1 q2 / 2
      radius_nonneg := by positivity
      mem_A := by
        intro t
        fin_cases t <;> simp [A2, L2]
      disk_mem := by
        intro t
        fin_cases t
        · simpa [L2, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            (le_of_eq (by
              simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                (dist_midpoint_left (𝕜 := ℝ) q1 q2)))
        · simpa [L2, dist_comm, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            (le_of_eq (by
              simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                (dist_midpoint_right (𝕜 := ℝ) q1 q2)))
      first_on_circle := by
        simpa [L2, Problem97.CGN.firstIndex, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (dist_left_midpoint (𝕜 := ℝ) q1 q2)
      last_on_circle := by
        simpa [L2, Problem97.CGN.lastIndex, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (dist_right_midpoint (𝕜 := ℝ) q1 q2) }
  let Hside2 : Problem97.CGN.MinorCapSideHypotheses P2 :=
    { cap_side_nonneg := by
        intro t
        fin_cases t <;> simp [L2, Problem97.CGN.firstIndex, Problem97.CGN.lastIndex, Problem97.signedArea2]
      center_side_nonpos := by
        simp [P2, L2, Problem97.CGN.firstIndex, Problem97.CGN.lastIndex, Problem97.signedArea2, midpoint_eq_smul_add]
        linarith }
  let Hord2 : Problem97.CGN.StrictCapOrder A2 L2 :=
    { hm := by decide
      consecutive_turn_nonpos := by
        intro t ht
        omega
      chord_projection_strict := by
        intro i j hij
        have hijval : i.val < j.val := Fin.lt_def.mp hij
        fin_cases i <;> fin_cases j
        · exfalso
          exact Nat.lt_irrefl 0 hijval
        · simpa [L2, Problem97.CGN.firstIndex, Problem97.CGN.lastIndex, real_inner_self_eq_norm_sq] using
            sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hqne.symm))
        · exfalso
          exact Nat.not_lt_zero 1 hijval
        · exfalso
          exact Nat.lt_irrefl 1 hijval
      subchord_open_side_iff_A := by
        intro r s hrs x hxA
        have hrsval : r.val < s.val := Fin.lt_def.mp hrs
        fin_cases r <;> fin_cases s
        · exfalso
          exact Nat.lt_irrefl 0 hrsval
        · constructor
          · intro hx
            exfalso
            simp [A2] at hxA
            rcases hxA with rfl | rfl
            · simp [L2, Problem97.signedArea2] at hx
            · simp [L2, Problem97.signedArea2] at hx
          · intro hx
            rcases hx with ⟨j, hrj, hjs, _⟩
            fin_cases j <;> omega
        · exfalso
          exact Nat.not_lt_zero 1 hrsval
        · exfalso
          exact Nat.lt_irrefl 1 hrsval }
  rcases Problem97.CGN.CGN6norm_minorCapChainModel_of_mecCapPacket P2 Hside2 Hord2 with
    ⟨T0, hT0, tau0, hModel⟩
  let LT0 : Problem97.CGN.OrderedCap 2 := L2.map T0 hT0
  let M0 : Problem97.CGN.MinorCapChainModel LT0 := Classical.choice hModel
  refine ⟨T0, tau0, ?_, ?_⟩
  · have hpt := M0.points_eq (Problem97.CGN.firstIndex (by decide : 2 ≤ 2))
    ext i <;> fin_cases i
    · calc
        (T0 q1) 0 = M0.coords.X (Problem97.CGN.firstIndex (by decide : 2 ≤ 2)) := by
          simpa [LT0, L2, Problem97.CGN.OrderedCap.map_points, Problem97.CGN.firstIndex,
            Problem97.CGN.point, Problem97.CGN.vec2, EuclideanSpace.single_apply]
            using congrArg (fun z : ℝ² => z 0) hpt
        _ = -1 := M0.coords.X_first
        _ = (Problem97.CGN.vec2 (-1) 0) 0 := by
          simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    · calc
        (T0 q1) 1 = M0.coords.Y (Problem97.CGN.firstIndex (by decide : 2 ≤ 2)) := by
          simpa [LT0, L2, Problem97.CGN.OrderedCap.map_points, Problem97.CGN.firstIndex,
            Problem97.CGN.point, Problem97.CGN.vec2, EuclideanSpace.single_apply]
            using congrArg (fun z : ℝ² => z 1) hpt
        _ = 0 := M0.coords.Y_first
        _ = (Problem97.CGN.vec2 (-1) 0) 1 := by
          simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
  · have hpt := M0.points_eq (Problem97.CGN.lastIndex (by decide : 2 ≤ 2))
    ext i <;> fin_cases i
    · calc
        (T0 q2) 0 = M0.coords.X (Problem97.CGN.lastIndex (by decide : 2 ≤ 2)) := by
          simpa [LT0, L2, Problem97.CGN.OrderedCap.map_points, Problem97.CGN.lastIndex,
            Problem97.CGN.point, Problem97.CGN.vec2, EuclideanSpace.single_apply]
            using congrArg (fun z : ℝ² => z 0) hpt
        _ = 1 := M0.coords.X_last
        _ = (Problem97.CGN.vec2 1 0) 0 := by
          simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    · calc
        (T0 q2) 1 = M0.coords.Y (Problem97.CGN.lastIndex (by decide : 2 ≤ 2)) := by
          simpa [LT0, L2, Problem97.CGN.OrderedCap.map_points, Problem97.CGN.lastIndex,
            Problem97.CGN.point, Problem97.CGN.vec2, EuclideanSpace.single_apply]
            using congrArg (fun z : ℝ² => z 1) hpt
        _ = 0 := M0.coords.Y_last
        _ = (Problem97.CGN.vec2 1 0) 1 := by
          simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
theorem i3_v3_a2_base_chord_side_signs_of_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)))
    {T0 : ℝ² → ℝ²} (tau : Problem97.CGN.SimilarityTransportData T0)
    (hv1 : T0 S.triangle.v1 = Problem97.CGN.vec2 (-1) 0)
    (hv2 : T0 S.triangle.v2 = Problem97.CGN.vec2 1 0)
    (ha2 : T0 Z.a2 = Problem97.CGN.vec2 0 (Real.sqrt 3)) :
    0 < (T0 S.triangle.v3) 1 ∧ ∀ x ∈ S.I3, (T0 x) 1 < 0 := by
  let q1 : ℝ² := S.triangle.v1
  let q2 : ℝ² := S.triangle.v2
  let q3 : ℝ² := S.triangle.v3
  let a : ℝ² := Z.a2
  have hside_a :
      signedArea2 a q1 q2 * signedArea2 q3 q1 q2 > 0 := by
    exact (b3n9m051_coreSupport S).C2_same_open_side_of_base_chord_as_v3 (Z := Z) hbranch hexact a (by simp [a, q3])
  have ha_img_pos :
      0 < signedArea2 (T0 a) (T0 q1) (T0 q2) := by
    rw [ha2, hv1, hv2, b3n9m051_signedArea2_baseChord_vec2]
    simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
  have himg_prod :
      0 < signedArea2 (T0 a) (T0 q1) (T0 q2) *
        signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
    rw [tau.halfplane_sign a q1 q2, tau.halfplane_sign q3 q1 q2]
    have hscale_sq_pos : 0 < tau.scale ^ 2 := sq_pos_of_ne_zero (ne_of_gt tau.scale_pos)
    have hrew :
        (tau.orientation * (tau.scale ^ 2) * signedArea2 a q1 q2) *
            (tau.orientation * (tau.scale ^ 2) * signedArea2 q3 q1 q2) =
          (tau.orientation ^ 2) * (tau.scale ^ 2 * tau.scale ^ 2) *
            (signedArea2 a q1 q2 * signedArea2 q3 q1 q2) := by
      ring
    rw [hrew]
    rw [tau.orientation_sq]
    exact mul_pos (mul_pos (by positivity) (mul_pos hscale_sq_pos hscale_sq_pos)) hside_a
  have hq3_img_pos :
      0 < signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
    have hle : 0 < signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
      by_contra hnot
      have hnonpos : signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 := by linarith
      have : signedArea2 (T0 a) (T0 q1) (T0 q2) *
          signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha_img_pos) hnonpos
      linarith
    exact hle
  have hq3_y_pos : 0 < (T0 q3) 1 := by
    rw [hv1, hv2] at hq3_img_pos
    rw [b3n9m051_signedArea2_baseChord_vec2] at hq3_img_pos
    linarith
  refine ⟨by simpa [q3] using hq3_y_pos, ?_⟩
  intro x hxI3
  have hxA : x ∈ A := S.CP.C3_subset (by
    unfold Problem97.FiniteEndpointShell.I3 at hxI3
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxI3))
  have hxC3 : x ∈ S.CP.C3 := by
    unfold Problem97.FiniteEndpointShell.I3 at hxI3
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxI3)
  have hx_ne_v1 : x ≠ q1 := by
    unfold Problem97.FiniteEndpointShell.I3 at hxI3
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hxI3).2).1
  have hx_ne_v2 : x ≠ q2 := by
    unfold Problem97.FiniteEndpointShell.I3 at hxI3
    exact (Finset.mem_erase.mp hxI3).1
  have hq3_base_ne : signedArea2 q3 q1 q2 ≠ 0 := by
    have hv1O : dist q3 S.Packet.center = S.Packet.radius := by
      simpa [q3, dist_eq_norm] using S.Packet.moser_on_boundary_3
    have hv2O : dist q1 S.Packet.center = S.Packet.radius := by
      simpa [q1, dist_eq_norm] using S.Packet.moser_on_boundary_1
    have hv3O : dist q2 S.Packet.center = S.Packet.radius := by
      simpa [q2, dist_eq_norm] using S.Packet.moser_on_boundary_2
    exact MEC.signedArea2_ne_zero_of_three_dist_eq
      hv1O hv2O hv3O
      S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
  have hx_arc :
      signedArea2 x q1 q2 * signedArea2 q3 q1 q2 ≤ 0 := by
    exact (S.CP.arc_membership x hxA).2.2.1 hxC3
  have hx_base_ne : signedArea2 x q1 q2 ≠ 0 := by
    intro hz
    have hcol : Collinear ℝ ({x, q1, q2} : Set ℝ²) :=
      (Problem97.signedArea2_eq_zero_iff_collinear x q1 q2).1 hz
    exact False.elim <|
      (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) hxA S.triangle.v1_mem S.triangle.v2_mem
        hx_ne_v1 hx_ne_v2 S.triangle.v12_ne hcol
  have himg_nonpos :
      signedArea2 (T0 x) (T0 q1) (T0 q2) *
        signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 := by
    rw [tau.halfplane_sign x q1 q2, tau.halfplane_sign q3 q1 q2]
    have hrew :
        (tau.orientation * (tau.scale ^ 2) * signedArea2 x q1 q2) *
            (tau.orientation * (tau.scale ^ 2) * signedArea2 q3 q1 q2) =
          (tau.orientation ^ 2) * (tau.scale ^ 2 * tau.scale ^ 2) *
            (signedArea2 x q1 q2 * signedArea2 q3 q1 q2) := by
      ring
    rw [hrew, tau.orientation_sq]
    have hscale_nonneg : 0 ≤ tau.scale ^ 2 * tau.scale ^ 2 := by positivity
    simpa using mul_nonpos_of_nonneg_of_nonpos hscale_nonneg hx_arc
  have hx_img_lt :
      signedArea2 (T0 x) (T0 q1) (T0 q2) < 0 := by
    have hx_img_le : signedArea2 (T0 x) (T0 q1) (T0 q2) ≤ 0 := by
      by_contra hx_pos
      have : 0 < signedArea2 (T0 x) (T0 q1) (T0 q2) *
          signedArea2 (T0 q3) (T0 q1) (T0 q2) :=
        mul_pos (by linarith) hq3_img_pos
      linarith
    have hx_img_ne : signedArea2 (T0 x) (T0 q1) (T0 q2) ≠ 0 := by
      rw [tau.halfplane_sign x q1 q2]
      have horient_ne : tau.orientation ≠ 0 := by
        intro h0
        have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tau.orientation_sq
        norm_num at this
      exact mul_ne_zero (mul_ne_zero horient_ne (pow_ne_zero 2 (ne_of_gt tau.scale_pos))) hx_base_ne
    exact lt_of_le_of_ne hx_img_le hx_img_ne
  rw [hv1, hv2] at hx_img_lt
  rw [b3n9m051_signedArea2_baseChord_vec2] at hx_img_lt
  linarith
theorem v1v3_longer_than_base_of_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s)
    (_hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3 := by
  classical
  rcases hbranch with ⟨⟨hA2, h_a2eq, h_v2eq⟩, _, _⟩
  have ha2T1 : Z.a2 ∈ S.witnessClassAt_v1 r := by
    have ha2mem : Z.a2 ∈ ({Z.a2} : Finset ℝ²) := by simp
    rw [← h_a2eq] at ha2mem
    exact (Finset.mem_inter.mp ha2mem).1
  have hv2T1 : S.triangle.v2 ∈ S.witnessClassAt_v1 r := by
    have hv2mem : S.triangle.v2 ∈ ({S.triangle.v2} : Finset ℝ²) := by simp
    rw [← h_v2eq] at hv2mem
    exact (Finset.mem_inter.mp hv2mem).1
  have hbase_eq : dist S.triangle.v1 S.triangle.v2 = dist S.triangle.v1 Z.a2 := by
    have hv2dist : dist S.triangle.v1 S.triangle.v2 = r := by
      simpa using (Finset.mem_filter.mp hv2T1).2
    have ha2dist : dist S.triangle.v1 Z.a2 = r := by
      simpa using (Finset.mem_filter.mp ha2T1).2
    rw [hv2dist, ha2dist]
  have ha2C2 : Z.a2 ∈ S.CP.C2 := by
    unfold Problem97.FiniteEndpointShell.I2 at hA2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).2
  have ha2_ne_v3 : Z.a2 ≠ S.triangle.v3 := by
    unfold Problem97.FiniteEndpointShell.I2 at hA2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).1
  have ha2_ne_v1 : Z.a2 ≠ S.triangle.v1 := by
    unfold Problem97.FiniteEndpointShell.I2 at hA2
    exact (Finset.mem_erase.mp hA2).1
  rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
      (A := A) (C := S.CP.C2) (M := S.triangle2)
      S.hconv S.hnoncol S.CP.C2_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.1)
      S.CP.v3_mem_C2 S.CP.v1_mem_C2 S.packet2 S.packet2.inner_at_v1 with
    ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
  have ha2L : Z.a2 ∈ Finset.univ.image L.points := by
    rw [hLC]
    exact ha2C2
  rcases Finset.mem_image.mp ha2L with ⟨i, -, hi⟩
  rcases hEnds with hFirstLast | hLastFirst
  · have hi_ne_first : i ≠ Problem97.CGN.firstIndex Packet.hm := by
      intro hi_first
      apply ha2_ne_v3
      calc
        Z.a2 = L.points i := hi.symm
        _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simpa [hi_first]
        _ = S.triangle.v3 := hFirstLast.1
    have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
      apply Fin.lt_def.mpr
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
      have hi_pos : 0 < i.val := by
        apply Nat.pos_of_ne_zero
        intro hi_zero
        apply hi_ne_first
        ext
        simpa [Problem97.CGN.firstIndex] using hi_zero
      omega
    have hmono :
        Problem97.FiniteEndpoint.E3L20b_rightEndpoint_capDistance_strict
          (L.points (Problem97.CGN.lastIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev L) :=
      Problem97.FiniteEndpoint.E3L20b_of_cgnCapData Packet Hside Hord
    have hlt :=
      hmono (i := i.rev) (j := Problem97.CGN.lastIndex Packet.hm) hi_rev_lt_last
    have hlast_rev_first : (Problem97.CGN.lastIndex Packet.hm).rev =
        Problem97.CGN.firstIndex Packet.hm := by
      ext
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
      simp [Problem97.CGN.firstIndex]
      omega
    have hlt' : dist S.triangle.v1 Z.a2 < dist S.triangle.v1 S.triangle.v3 := by
      simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points,
        hi, hFirstLast.1, hFirstLast.2, hlast_rev_first] using hlt
    simpa [hbase_eq] using hlt'
  · have hi_lt_last : i < Problem97.CGN.lastIndex Packet.hm := by
      apply Fin.lt_def.mpr
      rw [Problem97.CGN.lastIndex_val]
      have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
        intro hi_last
        apply ha2_ne_v3
        calc
          Z.a2 = L.points i := hi.symm
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simpa [hi_last]
          _ = S.triangle.v3 := hLastFirst.2
      have hi_lt_top : i.val < m := i.is_lt
      have hi_ne_top : i.val ≠ m - 1 := by
        intro hi_top
        apply hi_ne_last
        ext
        simpa [Problem97.CGN.lastIndex, Problem97.CGN.finIndex] using hi_top
      omega
    have hmono :
        Problem97.FiniteEndpoint.E3L20a_leftEndpoint_capDistance_strict
          (L.points (Problem97.CGN.firstIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap L) :=
      Problem97.FiniteEndpoint.E3L20a_of_cgnCapData Packet Hside Hord
    have hlt :=
      hmono (i := i) (j := Problem97.CGN.lastIndex Packet.hm) hi_lt_last
    have hlt' : dist S.triangle.v1 Z.a2 < dist S.triangle.v1 S.triangle.v3 := by
      simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points,
        hi, hLastFirst.1, hLastFirst.2] using hlt
    simpa [hbase_eq] using hlt'
theorem b3n9m051_v1b2_lt_v1v3_of_formB_v1_b2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r : ℝ}
    (hB : S.IsFormB_v1 r)
    (hxb2 : ∃ h : (Z.b2 : ℝ²) ∈ S.I2,
      S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²)) :
    dist S.triangle.v1 Z.b2 < dist S.triangle.v1 S.triangle.v3 := by
  classical
  rcases hxb2 with ⟨hB2, h_b2eq⟩
  rcases hB with ⟨x, hxI2, hxeq, hv2eq⟩
  have hb2T1 : Z.b2 ∈ S.witnessClassAt_v1 r := by
    have hb2mem : Z.b2 ∈ ({Z.b2} : Finset ℝ²) := by simp
    rw [← h_b2eq] at hb2mem
    exact (Finset.mem_inter.mp hb2mem).1
  have hv2T1 : S.triangle.v2 ∈ S.witnessClassAt_v1 r := by
    have hv2mem : S.triangle.v2 ∈ ({S.triangle.v2} : Finset ℝ²) := by simp
    rw [← hv2eq] at hv2mem
    exact (Finset.mem_inter.mp hv2mem).1
  have hbase_eq : dist S.triangle.v1 Z.b2 = dist S.triangle.v1 S.triangle.v2 := by
    have hv2dist : dist S.triangle.v1 S.triangle.v2 = r := by
      simpa using (Finset.mem_filter.mp hv2T1).2
    have hb2dist : dist S.triangle.v1 Z.b2 = r := by
      simpa using (Finset.mem_filter.mp hb2T1).2
    rw [hb2dist, hv2dist]
  have hb2C2 : Z.b2 ∈ S.CP.C2 := by
    unfold Problem97.FiniteEndpointShell.I2 at hB2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hB2).2).2
  have hb2_ne_v3 : Z.b2 ≠ S.triangle.v3 := by
    unfold Problem97.FiniteEndpointShell.I2 at hB2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hB2).2).1
  have hb2_ne_v1 : Z.b2 ≠ S.triangle.v1 := by
    unfold Problem97.FiniteEndpointShell.I2 at hB2
    exact (Finset.mem_erase.mp hB2).1
  rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
      (A := A) (C := S.CP.C2) (M := S.triangle2)
      S.hconv S.hnoncol S.CP.C2_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.1)
      S.CP.v3_mem_C2 S.CP.v1_mem_C2 S.packet2 S.packet2.inner_at_v1 with
    ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
  have hb2L : Z.b2 ∈ Finset.univ.image L.points := by
    rw [hLC]
    exact hb2C2
  rcases Finset.mem_image.mp hb2L with ⟨i, -, hi⟩
  rcases hEnds with hFirstLast | hLastFirst
  · have hi_ne_first : i ≠ Problem97.CGN.firstIndex Packet.hm := by
      intro hi_first
      apply hb2_ne_v3
      calc
        Z.b2 = L.points i := hi.symm
        _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simpa [hi_first]
        _ = S.triangle.v3 := hFirstLast.1
    have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
      apply Fin.lt_def.mpr
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
      have hi_pos : 0 < i.val := by
        apply Nat.pos_of_ne_zero
        intro hi_zero
        apply hi_ne_first
        ext
        simpa [Problem97.CGN.firstIndex] using hi_zero
      omega
    have hmono :
        Problem97.FiniteEndpoint.E3L20b_rightEndpoint_capDistance_strict
          (L.points (Problem97.CGN.lastIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev L) :=
      Problem97.FiniteEndpoint.E3L20b_of_cgnCapData Packet Hside Hord
    have hlt :=
      hmono (i := i.rev) (j := Problem97.CGN.lastIndex Packet.hm) hi_rev_lt_last
    have hlast_rev_first : (Problem97.CGN.lastIndex Packet.hm).rev =
        Problem97.CGN.firstIndex Packet.hm := by
      ext
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
      simp [Problem97.CGN.firstIndex]
      omega
    simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points,
      hi, hFirstLast.1, hFirstLast.2, hlast_rev_first] using hlt
  · have hi_lt_last : i < Problem97.CGN.lastIndex Packet.hm := by
      apply Fin.lt_def.mpr
      rw [Problem97.CGN.lastIndex_val]
      have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
        intro hi_last
        apply hb2_ne_v3
        calc
          Z.b2 = L.points i := hi.symm
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simpa [hi_last]
          _ = S.triangle.v3 := hLastFirst.2
      have hi_lt_top : i.val < m := i.is_lt
      have hi_ne_top : i.val ≠ m - 1 := by
        intro hi_top
        apply hi_ne_last
        ext
        simpa [Problem97.CGN.lastIndex, Problem97.CGN.finIndex] using hi_top
      omega
    have hmono :
        Problem97.FiniteEndpoint.E3L20a_leftEndpoint_capDistance_strict
          (L.points (Problem97.CGN.firstIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap L) :=
      Problem97.FiniteEndpoint.E3L20a_of_cgnCapData Packet Hside Hord
    have hlt :=
      hmono (i := i) (j := Problem97.CGN.lastIndex Packet.hm) hi_lt_last
    simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points,
      hi, hLastFirst.1, hLastFirst.2] using hlt
theorem b3n9m051_base_transport_a2_eq_upper
    {q1 q2 a : ℝ²} {T0 : ℝ² → ℝ²}
    (tau0 : Problem97.CGN.SimilarityTransportData T0)
    (hq1 : T0 q1 = Problem97.CGN.vec2 (-1) 0)
    (hq2 : T0 q2 = Problem97.CGN.vec2 1 0)
    (hleft : dist q1 a = dist q1 q2)
    (hright : dist q2 a = dist q2 q1)
    (hypos : 0 < (T0 a) 1) :
    T0 a = Problem97.CGN.vec2 0 (Real.sqrt 3) := by
  have hleft_img : dist (T0 q1) (T0 a) = dist (T0 q1) (T0 q2) := by
    exact (tau0.dist_eq_iff q1 a q2).2 hleft
  have hright_img : dist (T0 q2) (T0 a) = dist (T0 q2) (T0 q1) := by
    exact (tau0.dist_eq_iff q2 a q1).2 hright
  have hdist_left : dist (T0 a) (Problem97.CGN.vec2 (-1) 0) = 2 := by
    calc
      dist (T0 a) (Problem97.CGN.vec2 (-1) 0) = dist (T0 q1) (T0 a) := by
        rw [hq1, dist_comm]
      _ = dist (T0 q1) (T0 q2) := hleft_img
      _ = 2 := by
        rw [hq1, hq2]
        rw [dist_eq_norm]
        have hvec :
            Problem97.CGN.vec2 (-1) 0 - Problem97.CGN.vec2 1 0 =
              Problem97.CGN.vec2 (-2) 0 := by
          ext i <;> fin_cases i <;>
            simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
          · norm_num
        rw [hvec]
        rw [EuclideanSpace.norm_eq]
        norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
  have hdist_right : dist (T0 a) (Problem97.CGN.vec2 1 0) = 2 := by
    calc
      dist (T0 a) (Problem97.CGN.vec2 1 0) = dist (T0 q2) (T0 a) := by
        rw [hq2, dist_comm]
      _ = dist (T0 q2) (T0 q1) := hright_img
      _ = 2 := by
        rw [hq1, hq2]
        rw [dist_eq_norm]
        have hvec :
            Problem97.CGN.vec2 1 0 - Problem97.CGN.vec2 (-1) 0 =
              Problem97.CGN.vec2 2 0 := by
          ext i <;> fin_cases i <;>
            simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
          · norm_num
        rw [hvec]
        rw [EuclideanSpace.norm_eq]
        norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
  have hsq_left :
      ((T0 a) 0 + 1) ^ 2 + ((T0 a) 1) ^ 2 = 4 := by
    have hsq :
        ((T0 a) 0 + 1) ^ 2 + ((T0 a) 1) ^ 2 = dist (T0 a) (Problem97.CGN.vec2 (-1) 0) ^ 2 := by
      symm
      simpa [Problem97.CGN.vec2, EuclideanSpace.single_apply, add_comm, add_left_comm, add_assoc,
        sub_eq_add_neg] using
        (b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T0 a) (Problem97.CGN.vec2 (-1) 0))
    nlinarith only [hdist_left, hsq]
  have hsq_right :
      ((T0 a) 0 - 1) ^ 2 + ((T0 a) 1) ^ 2 = 4 := by
    have hsq :
        ((T0 a) 0 - 1) ^ 2 + ((T0 a) 1) ^ 2 = dist (T0 a) (Problem97.CGN.vec2 1 0) ^ 2 := by
      symm
      simpa [Problem97.CGN.vec2, EuclideanSpace.single_apply, add_comm, add_left_comm, add_assoc,
        sub_eq_add_neg] using
        (b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T0 a) (Problem97.CGN.vec2 1 0))
    nlinarith only [hdist_right, hsq]
  have hx0 : (T0 a) 0 = 0 := by
    nlinarith only [hsq_left, hsq_right]
  have hy_sq : ((T0 a) 1) ^ 2 = 3 := by
    nlinarith only [hsq_left, hsq_right, hx0]
  have hy_eq : (T0 a) 1 = Real.sqrt 3 := by
    have hsqeq : ((T0 a) 1) ^ 2 = (Real.sqrt 3) ^ 2 := by
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)]
      exact hy_sq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqeq with h | h
    · exact h
    · exfalso
      have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := by positivity
      have hy_nonneg : 0 ≤ (T0 a) 1 := le_of_lt hypos
      linarith
  ext i <;> fin_cases i
  · simpa [Problem97.CGN.vec2, EuclideanSpace.single_apply] using hx0
  · calc
      (T0 a) 1 = Real.sqrt 3 := hy_eq
      _ = (Problem97.CGN.vec2 0 (Real.sqrt 3)) 1 := by
        simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
theorem b3n9m051_delta_parameterization_of_normalized_apex
    (p : ℝ²)
    (hunit : dist p (Problem97.CGN.vec2 1 0) = 1)
    (hupper : 0 < p 1)
    (horigin_sq_le_two : dist (Problem97.CGN.vec2 0 0) p ^ 2 ≤ 2)
    (horigin_gt_one : 1 < dist (Problem97.CGN.vec2 0 0) p) :
    ∃ δ : ℝ,
      p =
        Problem97.CGN.vec2
          (2 * Real.cos δ * Real.cos δ)
          (2 * Real.cos δ * Real.sin δ) ∧
      Real.pi / 4 ≤ δ ∧
      δ < Real.pi / 3 := by
  let x : ℝ := p 0
  let y : ℝ := p 1
  let u : ℝ := x - 1
  have hcircle :
      u ^ 2 + y ^ 2 = 1 := by
    have hdist_sq : dist p (Problem97.CGN.vec2 1 0) ^ 2 = 1 := by
      have hnonneg : 0 ≤ dist p (Problem97.CGN.vec2 1 0) := dist_nonneg
      nlinarith only [hunit, hnonneg]
    have hcoord :
        dist p (Problem97.CGN.vec2 1 0) ^ 2 = u ^ 2 + y ^ 2 := by
      dsimp [u, x, y]
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq]
      simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    linarith
  have horigin_sq :
      dist (Problem97.CGN.vec2 0 0) p ^ 2 = x ^ 2 + y ^ 2 := by
    dsimp [x, y]
    rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq]
    simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
  have hx2y2_eq_twox : x ^ 2 + y ^ 2 = 2 * x := by
    dsimp [u] at hcircle
    nlinarith only [hcircle]
  have hx_le_one : x ≤ 1 := by
    rw [horigin_sq] at horigin_sq_le_two
    nlinarith only [horigin_sq_le_two, hcircle, hx2y2_eq_twox]
  have horigin_sq_gt_one : 1 < x ^ 2 + y ^ 2 := by
    rw [← horigin_sq]
    have hnonneg : 0 ≤ dist (Problem97.CGN.vec2 0 0) p := dist_nonneg
    nlinarith only [horigin_gt_one]
  have hx_gt_half : (1 : ℝ) / 2 < x := by
    nlinarith only [hcircle, horigin_sq_gt_one, hx2y2_eq_twox]
  have hu_le_zero : u ≤ 0 := by
    dsimp [u]
    linarith
  have hu_gt_neg_half : -(1 : ℝ) / 2 < u := by
    dsimp [u]
    linarith
  have hu_sq_lt_one : u ^ 2 < 1 := by
    have hy_sq_pos : 0 < y ^ 2 := sq_pos_of_pos (by simpa [y] using hupper)
    nlinarith only [hcircle, hy_sq_pos]
  have hu_bounds : -1 ≤ u ∧ u ≤ 1 := by
    constructor
    · nlinarith only [hu_sq_lt_one]
    · linarith
  let δ : ℝ := Real.arccos u / 2
  have hδ_lo : Real.pi / 4 ≤ δ := by
    have hhalf : Real.pi / 2 ≤ Real.arccos u := by
      by_contra hlt
      have hupos : 0 < u := by
        exact (Real.arccos_lt_pi_div_two).1 (lt_of_not_ge hlt)
      linarith
    dsimp [δ]
    linarith
  have harccos_neg_half :
      Real.arccos (-(1 / 2 : ℝ)) = 2 * Real.pi / 3 := by
    have harccos_half : Real.arccos ((1 : ℝ) / 2) = Real.pi / 3 := by
      have hlo : 0 ≤ Real.pi / 3 := by positivity
      have hhi : Real.pi / 3 ≤ Real.pi := by
        have hpi : 0 < Real.pi := Real.pi_pos
        linarith
      simpa [Real.cos_pi_div_three] using (Real.arccos_cos hlo hhi)
    rw [Real.arccos_neg, harccos_half]
    nlinarith only [Real.pi_pos]
  have hδ_hi : δ < Real.pi / 3 := by
    have hu_gt_neg_half' : (-(1 / 2 : ℝ)) < u := by
      have htmp := hu_gt_neg_half
      norm_num at htmp ⊢
      exact htmp
    have harccos_lt :
        Real.arccos u < 2 * Real.pi / 3 := by
      have hlt :=
        Real.arccos_lt_arccos (x := (-(1 / 2 : ℝ))) (y := u)
          (by norm_num) hu_gt_neg_half' hu_bounds.2
      rwa [harccos_neg_half] at hlt
    change Real.arccos u / 2 < Real.pi / 3
    linarith
  have hcos2δ : Real.cos (2 * δ) = u := by
    dsimp [δ]
    have htwo : 2 * (Real.arccos u / 2) = Real.arccos u := by ring
    rw [htwo, Real.cos_arccos hu_bounds.1 hu_bounds.2]
  have hy_sq :
      y ^ 2 = 1 - u ^ 2 := by
    nlinarith only [hcircle]
  have hy_eq_sqrt :
      y = Real.sqrt (1 - u ^ 2) := by
    have hnonneg : 0 ≤ 1 - u ^ 2 := by
      nlinarith only [hcircle, sq_nonneg y]
    have hsqeq : y ^ 2 = (Real.sqrt (1 - u ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt hnonneg]
      exact hy_sq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqeq with hy' | hy'
    · exact hy'
    · exfalso
      have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - u ^ 2) := by positivity
      have hy_nonneg : 0 ≤ y := le_of_lt (by simpa [y] using hupper)
      linarith
  have hsin2δ : Real.sin (2 * δ) = y := by
    dsimp [δ]
    have htwo : 2 * (Real.arccos u / 2) = Real.arccos u := by ring
    rw [htwo, Real.sin_arccos]
    exact hy_eq_sqrt.symm
  have hx_formula : x = 2 * Real.cos δ * Real.cos δ := by
    calc
      x = 1 + u := by
        dsimp [u]
        ring
      _ = 1 + Real.cos (2 * δ) := by rw [hcos2δ]
      _ = 2 * Real.cos δ * Real.cos δ := by
        rw [Real.cos_two_mul]
        nlinarith only [Real.sin_sq_add_cos_sq δ]
  have hy_formula : y = 2 * Real.cos δ * Real.sin δ := by
    calc
      y = Real.sin (2 * δ) := hsin2δ.symm
      _ = 2 * Real.sin δ * Real.cos δ := by rw [Real.sin_two_mul]
      _ = 2 * Real.cos δ * Real.sin δ := by ring
  refine ⟨δ, ?_, hδ_lo, hδ_hi⟩
  ext i <;> fin_cases i
  · simpa [x, Problem97.CGN.vec2, EuclideanSpace.single_apply] using hx_formula
  · simpa [y, Problem97.CGN.vec2, EuclideanSpace.single_apply] using hy_formula
set_option maxHeartbeats 8000000 in
theorem i3_v3_a2_delta_normalization_of_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) :
    S.I3V3A2DeltaNormalizationOfExactPacket Z := by
  classical
  intro r s hbranch hexact
  have hbranch0 := hbranch
  let q1 : ℝ² := S.triangle.v1
  let q2 : ℝ² := S.triangle.v2
  let q3 : ℝ² := S.triangle.v3
  let a : ℝ² := Z.a2
  rcases hbranch with ⟨⟨hA2, h_a2eq, h_v2eq⟩, hs_pos, hpacket⟩
  have haT1 : a ∈ S.witnessClassAt_v1 r := by
    have hamem : a ∈ ({a} : Finset ℝ²) := by simp
    rw [← h_a2eq] at hamem
    exact (Finset.mem_inter.mp hamem).1
  have hv2T1 : q2 ∈ S.witnessClassAt_v1 r := by
    have hv2mem : q2 ∈ ({q2} : Finset ℝ²) := by simp [q2]
    rw [← h_v2eq] at hv2mem
    exact (Finset.mem_inter.mp hv2mem).1
  have haT2 : a ∈ S.witnessClassAt_v2 s := by
    have hamem : a ∈ insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
      simp [a]
    rw [← hexact] at hamem
    exact hamem
  have hv1T2 : q1 ∈ S.witnessClassAt_v2 s := by
    have hv1mem : q1 ∈ insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
      simp [q1]
    rw [← hexact] at hv1mem
    exact hv1mem
  have hv3T2 : q3 ∈ S.witnessClassAt_v2 s := by
    have hv3mem : q3 ∈ insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
      simp [q3]
    rw [← hexact] at hv3mem
    exact hv3mem
  have hleft : dist q1 a = dist q1 q2 := by
    have hr_q1a : dist q1 a = r := by
      simpa [q1, a] using (Finset.mem_filter.mp haT1).2
    have hr_q1q2 : dist q1 q2 = r := by
      simpa [q1, q2] using (Finset.mem_filter.mp hv2T1).2
    rw [hr_q1a, hr_q1q2]
  have hright : dist q2 a = dist q2 q1 := by
    have hs_q2a : dist q2 a = s := by
      simpa [q2, a] using (Finset.mem_filter.mp haT2).2
    have hs_q2q1 : dist q2 q1 = s := by
      simpa [q1, q2] using (Finset.mem_filter.mp hv1T2).2
    rw [hs_q2a, hs_q2q1]
  have hq2q3_eq : dist q2 q3 = dist q2 q1 := by
    have hs_q2q3 : dist q2 q3 = s := by
      simpa [q2, q3] using (Finset.mem_filter.mp hv3T2).2
    have hs_q2q1 : dist q2 q1 = s := by
      simpa [q1, q2] using (Finset.mem_filter.mp hv1T2).2
    rw [hs_q2q3, hs_q2q1]
  have hinner_dist :
      dist q1 q3 ^ 2 ≤ dist q1 q2 ^ 2 + dist q2 q3 ^ 2 := by
    have hvec : q1 - q3 = (q1 - q2) - (q3 - q2) := by
      dsimp [q1, q2, q3]
      abel_nf
    have hinner : 0 ≤ inner ℝ (q3 - q2) (q1 - q2) := by
      simpa [q1, q2, q3] using S.Packet.inner_at_v2
    have hinner' : 0 ≤ inner ℝ (q1 - q2) (q3 - q2) := by
      simpa [real_inner_comm] using hinner
    calc
      dist q1 q3 ^ 2 = ‖q1 - q3‖ ^ 2 := by rw [dist_eq_norm]
      _ = ‖q1 - q2‖ ^ 2 - 2 * inner ℝ (q1 - q2) (q3 - q2) + ‖q3 - q2‖ ^ 2 := by
        rw [hvec, norm_sub_sq_real]
      _ ≤ ‖q1 - q2‖ ^ 2 + ‖q3 - q2‖ ^ 2 := by
        nlinarith only [hinner']
      _ = dist q1 q2 ^ 2 + dist q2 q3 ^ 2 := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        rw [norm_sub_rev]
  have hlong : dist q1 q2 < dist q1 q3 :=
    S.v1v3_longer_than_base_of_exact_packet (Z := Z) hbranch0 hexact
  have hq1ne : q1 ≠ q2 := by
    simpa [q1, q2] using S.triangle.v12_ne
  rcases b3n9m051_exists_base_transportData q1 q2 hq1ne with
    ⟨Tbase, tauBase, hv1Base, hv2Base⟩
  have horientBase_ne : tauBase.orientation ≠ 0 := by
    intro h0
    have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tauBase.orientation_sq
    norm_num at this
  have hq3_base_nonzero : (Tbase q3) 1 ≠ 0 := by
    have hq3_sa_ne :
        signedArea2 q3 q1 q2 ≠ 0 := by
      have hv1O : ‖q1 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q1] using S.Packet.moser_on_boundary_1
      have hv2O : ‖q2 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q2] using S.Packet.moser_on_boundary_2
      have hv3O : ‖q3 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q3] using S.Packet.moser_on_boundary_3
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        hv3O hv1O hv2O
        S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
    have himg_ne :
        signedArea2 (Tbase q3) (Tbase q1) (Tbase q2) ≠ 0 := by
      rw [tauBase.halfplane_sign q3 q1 q2]
      exact mul_ne_zero
        (mul_ne_zero horientBase_ne (pow_ne_zero 2 (ne_of_gt tauBase.scale_pos)))
        hq3_sa_ne
    intro h0
    apply himg_ne
    rw [hv1Base, hv2Base, b3n9m051_signedArea2_baseChord_vec2]
    linarith
  have build_from :
      ∀ {T0 : ℝ² → ℝ²},
        (tau0 : Problem97.CGN.SimilarityTransportData T0) →
        T0 q1 = Problem97.CGN.vec2 (-1) 0 →
        T0 q2 = Problem97.CGN.vec2 1 0 →
        0 < (T0 q3) 1 →
        S.I3V3A2DeltaNormalization Z := by
    intro T0 tau0 hv1 hv2 hq3y_pos
    have hside_a :
        signedArea2 a q1 q2 * signedArea2 q3 q1 q2 > 0 := by
      exact (b3n9m051_coreSupport S).C2_same_open_side_of_base_chord_as_v3 (Z := Z) hbranch0 hexact a (by simp [a, q3])
    have hq3_img_pos :
        0 < signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2]
      linarith
    have hprod_img :
        0 < signedArea2 (T0 a) (T0 q1) (T0 q2) *
          signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
      rw [tau0.halfplane_sign a q1 q2, tau0.halfplane_sign q3 q1 q2]
      have hscale_sq_pos : 0 < tau0.scale ^ 2 := sq_pos_of_ne_zero (ne_of_gt tau0.scale_pos)
      have hrew :
          (tau0.orientation * (tau0.scale ^ 2) * signedArea2 a q1 q2) *
              (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q3 q1 q2) =
            (tau0.orientation ^ 2) * (tau0.scale ^ 2 * tau0.scale ^ 2) *
              (signedArea2 a q1 q2 * signedArea2 q3 q1 q2) := by
        ring
      rw [hrew, tau0.orientation_sq]
      exact mul_pos (mul_pos (by positivity) (mul_pos hscale_sq_pos hscale_sq_pos)) hside_a
    have ha_img_pos :
        0 < signedArea2 (T0 a) (T0 q1) (T0 q2) := by
      by_contra hnot
      have hnonpos : signedArea2 (T0 a) (T0 q1) (T0 q2) ≤ 0 := by linarith
      have : signedArea2 (T0 a) (T0 q1) (T0 q2) *
          signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt hq3_img_pos)
      linarith
    have ha_y_pos : 0 < (T0 a) 1 := by
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2] at ha_img_pos
      linarith
    have ha2T0 : T0 a = Problem97.CGN.vec2 0 (Real.sqrt 3) := by
      exact b3n9m051_base_transport_a2_eq_upper tau0 hv1 hv2 hleft hright ha_y_pos
    rcases S.i3_v3_a2_base_chord_side_signs_of_exact_packet
        (Z := Z) hbranch0 hexact tau0 hv1 hv2 ha2T0 with
      ⟨hq3y_pos0, hbelow0⟩
    let T : ℝ² → ℝ² := fun x => b3n9m051_halfShift (T0 x)
    let tau : Problem97.CGN.SimilarityTransportData T :=
      b3n9m051_similarityTransportComp tau0 b3n9m051_halfShiftSimilarityTransportData
    have hv1T : T q1 = Problem97.CGN.vec2 0 0 := by
      dsimp [T]
      rw [hv1]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2T : T q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [T]
      rw [hv2]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have ha2T : T a = Problem97.CGN.vec2 ((1 : ℝ) / 2) (Real.sqrt 3 / 2) := by
      dsimp [T]
      rw [ha2T0]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hbelow :
        ∀ x ∈ S.I3, (T x) 1 < 0 := by
      intro x hxI3
      dsimp [T]
      have hxlt := hbelow0 x hxI3
      simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      linarith
    have hq3y_T : 0 < (T q3) 1 := by
      dsimp [T]
      simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      linarith
    have hdist_q2q3 :
        dist (T q2) (T q3) = dist (T q2) (T q1) := by
      exact (tau.dist_eq_iff q2 q3 q1).2 hq2q3_eq
    have hbase_dist :
        dist (T q2) (T q1) = 1 := by
      rw [hv2T, hv1T, dist_eq_norm]
      have hvec :
          Problem97.CGN.vec2 1 0 - Problem97.CGN.vec2 0 0 =
            Problem97.CGN.vec2 1 0 := by
        ext i <;> fin_cases i <;>
          simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
      rw [hvec, EuclideanSpace.norm_eq]
      norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hdist_q2q3_one : dist (T q2) (T q3) = 1 := by
      rw [hdist_q2q3, hbase_dist]
    have hnonobtuse_T :
        dist (T q1) (T q3) ^ 2 ≤ dist (T q1) (T q2) ^ 2 + dist (T q2) (T q3) ^ 2 := by
      have hmul :
          tau.scale ^ 2 * dist q1 q3 ^ 2 ≤
            tau.scale ^ 2 * (dist q1 q2 ^ 2 + dist q2 q3 ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinner_dist (sq_nonneg tau.scale)
      have hscaled :
          (tau.scale * dist q1 q3) ^ 2 ≤
            (tau.scale * dist q1 q2) ^ 2 + (tau.scale * dist q2 q3) ^ 2 := by
        nlinarith only [hmul]
      simpa [tau.dist_image] using hscaled
    have hlong_T : dist (T q1) (T q2) < dist (T q1) (T q3) := by
      rw [tau.dist_image, tau.dist_image]
      nlinarith only [hlong, tau.scale_pos]
    have horigin_sq_le_two :
        dist (Problem97.CGN.vec2 0 0) (T q3) ^ 2 ≤ 2 := by
      have hdist_q1q2_sq :
          dist (T q1) (T q2) ^ 2 = 1 := by
        have hdist : dist (T q1) (T q2) = 1 := by
          rw [dist_comm]
          exact hbase_dist
        have hnonneg : 0 ≤ dist (T q1) (T q2) := dist_nonneg
        nlinarith only [hdist, hnonneg]
      have hdist_q2q3_sq :
          dist (T q2) (T q3) ^ 2 = 1 := by
        have hnonneg : 0 ≤ dist (T q2) (T q3) := dist_nonneg
        nlinarith only [hdist_q2q3, hbase_dist, hdist_q2q3_one, hnonneg]
      have htmp := hnonobtuse_T
      rw [hdist_q1q2_sq, hdist_q2q3_sq] at htmp
      have : dist (Problem97.CGN.vec2 0 0) (T q3) ^ 2 ≤ 2 := by
        have htmp' : dist (Problem97.CGN.vec2 0 0) (T q3) ^ 2 ≤ 1 + 1 := by
          simpa [hv1T, dist_comm] using htmp
        nlinarith only [htmp']
      exact this
    have horigin_gt_one :
        1 < dist (Problem97.CGN.vec2 0 0) (T q3) := by
      have h01 : dist (Problem97.CGN.vec2 0 0) (Problem97.CGN.vec2 1 0) = 1 := by
        rw [dist_eq_norm]
        have hvec :
            Problem97.CGN.vec2 0 0 - Problem97.CGN.vec2 1 0 =
              Problem97.CGN.vec2 (-1) 0 := by
          ext i <;> fin_cases i <;>
            simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
        rw [hvec, EuclideanSpace.norm_eq]
        norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have hlong_T' := hlong_T
      rw [hv1T, hv2T] at hlong_T'
      simpa [h01] using hlong_T'
    have hunit_T :
        dist (T q3) (Problem97.CGN.vec2 1 0) = 1 := by
      simpa [hv2T, dist_comm] using hdist_q2q3_one
    rcases b3n9m051_delta_parameterization_of_normalized_apex
        (p := T q3) hunit_T hq3y_T horigin_sq_le_two horigin_gt_one with
      ⟨δ, hv3T, hδ_lo, hδ_hi⟩
    refine ⟨T, tau, δ, hv1T, hv2T, ha2T, hv3T, hδ_lo, hδ_hi, hbelow⟩
  by_cases hq3pos : 0 < (Tbase q3) 1
  · exact build_from tauBase hv1Base hv2Base hq3pos
  · let Tflip : ℝ² → ℝ² := fun x => b3n9m051_flipY (Tbase x)
    let tauFlip : Problem97.CGN.SimilarityTransportData Tflip :=
      b3n9m051_similarityTransportComp tauBase b3n9m051_flipYSimilarityTransportData
    have hv1Flip : Tflip q1 = Problem97.CGN.vec2 (-1) 0 := by
      dsimp [Tflip]
      rw [hv1Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2Flip : Tflip q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [Tflip]
      rw [hv2Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3Flip : 0 < (Tflip q3) 1 := by
      dsimp [Tflip]
      simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have hq3neg : (Tbase q3) 1 < 0 := by
        have hle : (Tbase q3) 1 ≤ 0 := le_of_not_gt hq3pos
        exact lt_of_le_of_ne hle hq3_base_nonzero
      linarith
    exact build_from tauFlip hv1Flip hv2Flip hq3Flip
theorem i3_v3_a2_normalized_height_gap_of_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    S.I3V3A2NormalizedHeightGap Z := by
  have hdelta : S.I3V3A2DeltaNormalizationOfExactPacket Z :=
    S.i3_v3_a2_delta_normalization_of_exact_packet Z
  exact (b3n9m051_coreSupport S).i3_v3_a2_normalized_height_gap_of_delta_normalization Z
    (hdelta hbranch hexact)
theorem i3_no_point_on_v3_radius_at_a2_of_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    S.I3NoPointOnV3RadiusAtA2 Z := by
  exact (b3n9m051_coreSupport S).i3_no_point_on_v3_radius_at_a2_of_normalized_height_gap Z
    (S.i3_v3_a2_normalized_height_gap_of_exact_packet Z hbranch hexact)
theorem i3_on_v3_radius_at_a2_card_le_one_of_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    S.I3OnV3RadiusAtA2CardLeOne Z := by
  exact (b3n9m051_coreSupport S).i3_on_v3_radius_at_a2_card_le_one_of_no_hit Z
    (S.i3_no_point_on_v3_radius_at_a2_of_exact_packet Z hbranch hexact)
theorem selectorShape_v3_q_eq_a2_impossible_of_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)))
    (hpacket : SelectorV3Qa2Packet S Z t) :
    False := by
  exact (b3n9m051_coreSupport S).selectorShape_v3_q_eq_a2_impossible Z hpacket
    (S.i3_on_v3_radius_at_a2_card_le_one_of_exact_packet Z hbranch hexact)
theorem n4d_bB_2_q_eq_v1_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hlower : FormBv1B2SelectorV2LowerPacket S Z r s)
    (hpacket3 : SelectorV3Qv1Packet S Z t) :
    False := by
  classical
  rcases hlower with ⟨hB2, hb2eq, hTcard, hI2sub, hC1eq, hC3eq⟩
  let T := S.witnessClassAt_v2 s
  have hv3T : S.triangle.v3 ∈ T := by
    have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    rw [← hC1eq] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hq :
      (Z.a3 : ℝ²) ∈ T ∩ S.CP.C3 ∨ (Z.b3 : ℝ²) ∈ T ∩ S.CP.C3 := by
    rcases hC3eq with hqa3 | hqb3
    · left
      have hmem : Z.a3 ∈ ({Z.a3} : Finset ℝ²) := by simp
      rw [← hqa3] at hmem
      exact hmem
    · right
      have hmem : Z.b3 ∈ ({Z.b3} : Finset ℝ²) := by simp
      rw [← hqb3] at hmem
      exact hmem
  obtain ⟨q, hqI3, hqT2⟩ : ∃ q : ℝ², q ∈ S.I3 ∧ q ∈ T := by
    rcases hq with hqa3 | hqb3
    · refine ⟨Z.a3, ?_, ?_⟩
      · rw [Z.hI3]
        simp
      · exact (Finset.mem_inter.mp hqa3).1
    · refine ⟨Z.b3, ?_, ?_⟩
      · rw [Z.hI3]
        simp
      · exact (Finset.mem_inter.mp hqb3).1
  have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
    simpa using (Finset.mem_filter.mp hv3T).2
  have hqrad : dist S.triangle.v2 q = s := by
    simpa using (Finset.mem_filter.mp hqT2).2
  have hq_lt_base : dist S.triangle.v2 q < dist S.triangle.v2 S.triangle.v1 := by
    rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
        (A := A) (C := S.CP.C3) (M := S.triangle3)
        S.hconv S.hnoncol S.CP.C3_subset
        (fun x hxA => (S.CP.arc_membership x hxA).2.2)
        S.CP.v1_mem_C3 S.CP.v2_mem_C3 S.packet3 S.packet3.inner_at_v1 with
      ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
    have hqC3 : q ∈ S.CP.C3 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3)
    have hqL : q ∈ Finset.univ.image L.points := by
      rw [hLC]
      exact hqC3
    rcases Finset.mem_image.mp hqL with ⟨i, -, hi⟩
    have hq_ne_v2 : q ≠ S.triangle.v2 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp hqI3).1
    have hq_ne_v1 : q ≠ S.triangle.v1 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqI3).2).1
    rcases hEnds with hFirstLast | hLastFirst
    · have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
        intro hi_last
        apply hq_ne_v2
        calc
          q = L.points i := hi.symm
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simpa [hi_last]
          _ = S.triangle.v2 := hFirstLast.2
      have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
        apply Fin.lt_def.mpr
        rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
        have hi_lt_top : i.val < m := i.is_lt
        have hi_ne_zero : i.val ≠ 0 := by
          intro hi_zero
          have hi_first : i = Problem97.CGN.firstIndex Packet.hm := by
            ext
            simpa [Problem97.CGN.firstIndex] using hi_zero
          apply hq_ne_v1
          calc
            q = L.points i := hi.symm
            _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simpa [hi_first]
            _ = S.triangle.v1 := hFirstLast.1
        omega
      have hmono :
          Problem97.FiniteEndpoint.E3L20b_rightEndpoint_capDistance_strict
            (L.points (Problem97.CGN.lastIndex Packet.hm))
            (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev L) :=
        Problem97.FiniteEndpoint.E3L20b_of_cgnCapData Packet Hside Hord
      have hlt :=
        hmono (i := i.rev) (j := Problem97.CGN.lastIndex Packet.hm) hi_rev_lt_last
      have hlast_rev_first :
          (Problem97.CGN.lastIndex Packet.hm).rev = Problem97.CGN.firstIndex Packet.hm := by
        ext
        rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
        simp [Problem97.CGN.firstIndex]
        omega
      simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points,
        hi, hFirstLast.1, hFirstLast.2, hlast_rev_first] using hlt
    · have hi_lt_last : i < Problem97.CGN.lastIndex Packet.hm := by
        apply Fin.lt_def.mpr
        rw [Problem97.CGN.lastIndex_val]
        have hi_lt_top : i.val < m := i.is_lt
        have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
          intro hi_last
          apply hq_ne_v1
          calc
            q = L.points i := hi.symm
            _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simpa [hi_last]
            _ = S.triangle.v1 := hLastFirst.2
        have hi_ne_top : i.val ≠ m - 1 := by
          intro hi_top
          apply hi_ne_last
          ext
          simpa [Problem97.CGN.lastIndex, Problem97.CGN.finIndex] using hi_top
        omega
      have hmono :
          Problem97.FiniteEndpoint.E3L20a_leftEndpoint_capDistance_strict
            (L.points (Problem97.CGN.firstIndex Packet.hm))
            (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap L) :=
        Problem97.FiniteEndpoint.E3L20a_of_cgnCapData Packet Hside Hord
      have hlt :=
        hmono (i := i) (j := Problem97.CGN.lastIndex Packet.hm) hi_lt_last
      simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points,
        hi, hLastFirst.1, hLastFirst.2] using hlt
  have hbase_lt_long : dist S.triangle.v2 S.triangle.v1 < dist S.triangle.v3 S.triangle.v1 := by
    have hb2T1 : Z.b2 ∈ S.witnessClassAt_v1 r := by
      have hb2mem : Z.b2 ∈ ({Z.b2} : Finset ℝ²) := by simp
      rw [← hb2eq] at hb2mem
      exact (Finset.mem_inter.mp hb2mem).1
    have hv2T1 : S.triangle.v2 ∈ S.witnessClassAt_v1 r := by
      rcases hB with ⟨x, hxI2, hxeq, hv2eq⟩
      have hv2mem : S.triangle.v2 ∈ ({S.triangle.v2} : Finset ℝ²) := by simp
      rw [← hv2eq] at hv2mem
      exact (Finset.mem_inter.mp hv2mem).1
    have hbase_eq : dist S.triangle.v1 S.triangle.v2 = dist S.triangle.v1 Z.b2 := by
      have hv2dist : dist S.triangle.v1 S.triangle.v2 = r := by
        simpa using (Finset.mem_filter.mp hv2T1).2
      have hb2dist : dist S.triangle.v1 Z.b2 = r := by
        simpa using (Finset.mem_filter.mp hb2T1).2
      rw [hv2dist, hb2dist]
    have h := S.b3n9m051_v1b2_lt_v1v3_of_formB_v1_b2 Z hB ⟨hB2, hb2eq⟩
    simpa [hbase_eq, dist_comm] using h
  have hv2v1 : dist S.triangle.v3 S.triangle.v2 < dist S.triangle.v3 S.triangle.v1 := by
    calc
      dist S.triangle.v3 S.triangle.v2 = dist S.triangle.v2 S.triangle.v3 := by rw [dist_comm]
      _ = dist S.triangle.v2 q := by rw [hqrad, hv3rad]
      _ < dist S.triangle.v2 S.triangle.v1 := hq_lt_base
      _ < dist S.triangle.v3 S.triangle.v1 := hbase_lt_long
  exact (b3n9m051_coreSupport S).selectorShape_v3_q_eq_v1_impossible Z hpacket3 hv2v1
theorem b3n9m051_v1_lt_v1v3_of_mem_I2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {p : ℝ²}
    (hpI2 : p ∈ S.I2) :
    dist S.triangle.v1 p < dist S.triangle.v1 S.triangle.v3 := by
  classical
  have hpC2 : p ∈ S.CP.C2 := by
    unfold Problem97.FiniteEndpointShell.I2 at hpI2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hpI2).2).2
  have hp_ne_v3 : p ≠ S.triangle.v3 := by
    unfold Problem97.FiniteEndpointShell.I2 at hpI2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hpI2).2).1
  have hp_ne_v1 : p ≠ S.triangle.v1 := by
    unfold Problem97.FiniteEndpointShell.I2 at hpI2
    exact (Finset.mem_erase.mp hpI2).1
  rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
      (A := A) (C := S.CP.C2) (M := S.triangle2)
      S.hconv S.hnoncol S.CP.C2_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.1)
      S.CP.v3_mem_C2 S.CP.v1_mem_C2 S.packet2 S.packet2.inner_at_v1 with
    ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
  have hpL : p ∈ Finset.univ.image L.points := by
    rw [hLC]
    exact hpC2
  rcases Finset.mem_image.mp hpL with ⟨i, -, hi⟩
  rcases hEnds with hFirstLast | hLastFirst
  · have hi_ne_first : i ≠ Problem97.CGN.firstIndex Packet.hm := by
      intro hi_first
      apply hp_ne_v3
      calc
        p = L.points i := hi.symm
        _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simpa [hi_first]
        _ = S.triangle.v3 := hFirstLast.1
    have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
      apply Fin.lt_def.mpr
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
      have hi_pos : 0 < i.val := by
        apply Nat.pos_of_ne_zero
        intro hi_zero
        apply hi_ne_first
        ext
        simpa [Problem97.CGN.firstIndex] using hi_zero
      omega
    have hmono :
        Problem97.FiniteEndpoint.E3L20b_rightEndpoint_capDistance_strict
          (L.points (Problem97.CGN.lastIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev L) :=
      Problem97.FiniteEndpoint.E3L20b_of_cgnCapData Packet Hside Hord
    have hlt :=
      hmono (i := i.rev) (j := Problem97.CGN.lastIndex Packet.hm) hi_rev_lt_last
    have hlast_rev_first : (Problem97.CGN.lastIndex Packet.hm).rev =
        Problem97.CGN.firstIndex Packet.hm := by
      ext
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
      simp [Problem97.CGN.firstIndex]
      omega
    simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points,
      hi, hFirstLast.1, hFirstLast.2, hlast_rev_first] using hlt
  · have hi_lt_last : i < Problem97.CGN.lastIndex Packet.hm := by
      apply Fin.lt_def.mpr
      rw [Problem97.CGN.lastIndex_val]
      have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
        intro hi_last
        apply hp_ne_v3
        calc
          p = L.points i := hi.symm
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simpa [hi_last]
          _ = S.triangle.v3 := hLastFirst.2
      have hi_lt_top : i.val < m := i.is_lt
      have hi_ne_top : i.val ≠ m - 1 := by
        intro hi_top
        apply hi_ne_last
        ext
        simpa [Problem97.CGN.lastIndex, Problem97.CGN.finIndex] using hi_top
      omega
    have hmono :
        Problem97.FiniteEndpoint.E3L20a_leftEndpoint_capDistance_strict
          (L.points (Problem97.CGN.firstIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap L) :=
      Problem97.FiniteEndpoint.E3L20a_of_cgnCapData Packet Hside Hord
    have hlt :=
      hmono (i := i) (j := Problem97.CGN.lastIndex Packet.hm) hi_lt_last
    simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points,
      hi, hLastFirst.1, hLastFirst.2] using hlt
theorem n4d_bA_2_q_eq_v1_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hlower : FormBv1A2SelectorV2LowerPacket S Z r s)
    (hpacket3 : SelectorV3Qv1Packet S Z t) :
    False := by
  classical
  rcases hlower with ⟨hA2, ha2eq, hTcard, hI2sub, hC1eq, hC3eq⟩
  let T := S.witnessClassAt_v2 s
  have hv3T : S.triangle.v3 ∈ T := by
    have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    rw [← hC1eq] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hq :
      (Z.a3 : ℝ²) ∈ T ∩ S.CP.C3 ∨ (Z.b3 : ℝ²) ∈ T ∩ S.CP.C3 := by
    rcases hC3eq with hqa3 | hqb3
    · left
      have hmem : Z.a3 ∈ ({Z.a3} : Finset ℝ²) := by simp
      rw [← hqa3] at hmem
      exact hmem
    · right
      have hmem : Z.b3 ∈ ({Z.b3} : Finset ℝ²) := by simp
      rw [← hqb3] at hmem
      exact hmem
  obtain ⟨q, hqI3, hqT2⟩ : ∃ q : ℝ², q ∈ S.I3 ∧ q ∈ T := by
    rcases hq with hqa3 | hqb3
    · refine ⟨Z.a3, ?_, ?_⟩
      · rw [Z.hI3]
        simp
      · exact (Finset.mem_inter.mp hqa3).1
    · refine ⟨Z.b3, ?_, ?_⟩
      · rw [Z.hI3]
        simp
      · exact (Finset.mem_inter.mp hqb3).1
  have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
    simpa using (Finset.mem_filter.mp hv3T).2
  have hqrad : dist S.triangle.v2 q = s := by
    simpa using (Finset.mem_filter.mp hqT2).2
  have hq_lt_base : dist S.triangle.v2 q < dist S.triangle.v2 S.triangle.v1 := by
    rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
        (A := A) (C := S.CP.C3) (M := S.triangle3)
        S.hconv S.hnoncol S.CP.C3_subset
        (fun x hxA => (S.CP.arc_membership x hxA).2.2)
        S.CP.v1_mem_C3 S.CP.v2_mem_C3 S.packet3 S.packet3.inner_at_v1 with
      ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
    have hqC3 : q ∈ S.CP.C3 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3)
    have hqL : q ∈ Finset.univ.image L.points := by
      rw [hLC]
      exact hqC3
    rcases Finset.mem_image.mp hqL with ⟨i, -, hi⟩
    have hq_ne_v2 : q ≠ S.triangle.v2 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp hqI3).1
    have hq_ne_v1 : q ≠ S.triangle.v1 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqI3).2).1
    rcases hEnds with hFirstLast | hLastFirst
    · have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
        intro hi_last
        apply hq_ne_v2
        calc
          q = L.points i := hi.symm
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simpa [hi_last]
          _ = S.triangle.v2 := hFirstLast.2
      have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
        apply Fin.lt_def.mpr
        rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
        have hi_lt_top : i.val < m := i.is_lt
        have hi_ne_zero : i.val ≠ 0 := by
          intro hi_zero
          have hi_first : i = Problem97.CGN.firstIndex Packet.hm := by
            ext
            simpa [Problem97.CGN.firstIndex] using hi_zero
          apply hq_ne_v1
          calc
            q = L.points i := hi.symm
            _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simpa [hi_first]
            _ = S.triangle.v1 := hFirstLast.1
        omega
      have hmono :
          Problem97.FiniteEndpoint.E3L20b_rightEndpoint_capDistance_strict
            (L.points (Problem97.CGN.lastIndex Packet.hm))
            (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev L) :=
        Problem97.FiniteEndpoint.E3L20b_of_cgnCapData Packet Hside Hord
      have hlt :=
        hmono (i := i.rev) (j := Problem97.CGN.lastIndex Packet.hm) hi_rev_lt_last
      have hlast_rev_first :
          (Problem97.CGN.lastIndex Packet.hm).rev = Problem97.CGN.firstIndex Packet.hm := by
        ext
        rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
        simp [Problem97.CGN.firstIndex]
        omega
      simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points,
        hi, hFirstLast.1, hFirstLast.2, hlast_rev_first] using hlt
    · have hi_lt_last : i < Problem97.CGN.lastIndex Packet.hm := by
        apply Fin.lt_def.mpr
        rw [Problem97.CGN.lastIndex_val]
        have hi_lt_top : i.val < m := i.is_lt
        have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
          intro hi_last
          apply hq_ne_v1
          calc
            q = L.points i := hi.symm
            _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simpa [hi_last]
            _ = S.triangle.v1 := hLastFirst.2
        have hi_ne_top : i.val ≠ m - 1 := by
          intro hi_top
          apply hi_ne_last
          ext
          simpa [Problem97.CGN.lastIndex, Problem97.CGN.finIndex] using hi_top
        omega
      have hmono :
          Problem97.FiniteEndpoint.E3L20a_leftEndpoint_capDistance_strict
            (L.points (Problem97.CGN.firstIndex Packet.hm))
            (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap L) :=
        Problem97.FiniteEndpoint.E3L20a_of_cgnCapData Packet Hside Hord
      have hlt :=
        hmono (i := i) (j := Problem97.CGN.lastIndex Packet.hm) hi_lt_last
      simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points,
        hi, hLastFirst.1, hLastFirst.2] using hlt
  have hbase_lt_long : dist S.triangle.v2 S.triangle.v1 < dist S.triangle.v3 S.triangle.v1 := by
    have ha2T1 : Z.a2 ∈ S.witnessClassAt_v1 r := by
      have ha2mem : Z.a2 ∈ ({Z.a2} : Finset ℝ²) := by simp
      rw [← ha2eq] at ha2mem
      exact (Finset.mem_inter.mp ha2mem).1
    have hv2T1 : S.triangle.v2 ∈ S.witnessClassAt_v1 r := by
      rcases hB with ⟨x, hxI2, hxeq, hv2eq⟩
      have hv2mem : S.triangle.v2 ∈ ({S.triangle.v2} : Finset ℝ²) := by simp
      rw [← hv2eq] at hv2mem
      exact (Finset.mem_inter.mp hv2mem).1
    have hbase_eq : dist S.triangle.v1 S.triangle.v2 = dist S.triangle.v1 Z.a2 := by
      have hv2dist : dist S.triangle.v1 S.triangle.v2 = r := by
        simpa using (Finset.mem_filter.mp hv2T1).2
      have ha2dist : dist S.triangle.v1 Z.a2 = r := by
        simpa using (Finset.mem_filter.mp ha2T1).2
      rw [hv2dist, ha2dist]
    have h := S.b3n9m051_v1_lt_v1v3_of_mem_I2 (p := Z.a2) hA2
    simpa [hbase_eq, dist_comm] using h
  have hv2v1 : dist S.triangle.v3 S.triangle.v2 < dist S.triangle.v3 S.triangle.v1 := by
    calc
      dist S.triangle.v3 S.triangle.v2 = dist S.triangle.v2 S.triangle.v3 := by rw [dist_comm]
      _ = dist S.triangle.v2 q := by rw [hqrad, hv3rad]
      _ < dist S.triangle.v2 S.triangle.v1 := hq_lt_base
      _ < dist S.triangle.v3 S.triangle.v1 := hbase_lt_long
  exact (b3n9m051_coreSupport S).selectorShape_v3_q_eq_v1_impossible Z hpacket3 hv2v1
theorem b3n9m051_v1_lt_v1v2_of_mem_I3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {q : ℝ²}
    (hqI3 : q ∈ S.I3) :
    dist S.triangle.v1 q < dist S.triangle.v1 S.triangle.v2 := by
  classical
  have hqC3 : q ∈ S.CP.C3 := by
    unfold Problem97.FiniteEndpointShell.I3 at hqI3
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3)
  have hq_ne_v2 : q ≠ S.triangle.v2 := by
    unfold Problem97.FiniteEndpointShell.I3 at hqI3
    exact (Finset.mem_erase.mp hqI3).1
  have hq_ne_v1 : q ≠ S.triangle.v1 := by
    unfold Problem97.FiniteEndpointShell.I3 at hqI3
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqI3).2).1
  rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
      (A := A) (C := S.CP.C3) (M := S.triangle3)
      S.hconv S.hnoncol S.CP.C3_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.2)
      S.CP.v1_mem_C3 S.CP.v2_mem_C3 S.packet3 S.packet3.inner_at_v1 with
    ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
  have hqL : q ∈ Finset.univ.image L.points := by
    rw [hLC]
    exact hqC3
  rcases Finset.mem_image.mp hqL with ⟨i, -, hi⟩
  rcases hEnds with hFirstLast | hLastFirst
  ·
    have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
      intro hi_last
      apply hq_ne_v2
      calc
        q = L.points i := hi.symm
        _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simpa [hi_last]
        _ = S.triangle.v2 := hFirstLast.2
    have hi_lt_last : i < Problem97.CGN.lastIndex Packet.hm := by
      apply Fin.lt_def.mpr
      rw [Problem97.CGN.lastIndex_val]
      have hi_lt_top : i.val < m := i.is_lt
      have hi_ne_top : i.val ≠ m - 1 := by
        intro hi_top
        apply hi_ne_last
        ext
        simpa [Problem97.CGN.lastIndex, Problem97.CGN.finIndex] using hi_top
      omega
    have hmono :
        Problem97.FiniteEndpoint.E3L20a_leftEndpoint_capDistance_strict
          (L.points (Problem97.CGN.firstIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap L) :=
      Problem97.FiniteEndpoint.E3L20a_of_cgnCapData Packet Hside Hord
    have hlt :=
      hmono (i := i) (j := Problem97.CGN.lastIndex Packet.hm) hi_lt_last
    simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points,
      hi, hFirstLast.1, hFirstLast.2] using hlt
  ·
    have hi_ne_first : i ≠ Problem97.CGN.firstIndex Packet.hm := by
      intro hi_first
      apply hq_ne_v2
      calc
        q = L.points i := hi.symm
        _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simpa [hi_first]
        _ = S.triangle.v2 := hLastFirst.1
    have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
      apply Fin.lt_def.mpr
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
      have hi_pos : 0 < i.val := by
        apply Nat.pos_of_ne_zero
        intro hi_zero
        apply hi_ne_first
        ext
        simpa [Problem97.CGN.firstIndex] using hi_zero
      omega
    have hmono :
        Problem97.FiniteEndpoint.E3L20b_rightEndpoint_capDistance_strict
          (L.points (Problem97.CGN.lastIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev L) :=
      Problem97.FiniteEndpoint.E3L20b_of_cgnCapData Packet Hside Hord
    have hlt :=
      hmono (i := i.rev) (j := Problem97.CGN.lastIndex Packet.hm) hi_rev_lt_last
    have hlast_rev_first : (Problem97.CGN.lastIndex Packet.hm).rev =
        Problem97.CGN.firstIndex Packet.hm := by
      ext
      rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
      simp [Problem97.CGN.firstIndex]
      omega
    simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points,
      hi, hLastFirst.1, hLastFirst.2, hlast_rev_first] using hlt
theorem b3n9m051_pEqB_lower_apex_dist_contradiction
    (A B q : ℝ²) (r δ a b : ℝ) (hr : 0 < r)
    (hA : A = Problem97.CGN.vec2 0 0) (hB : B = Problem97.CGN.vec2 1 0)
    (hq : q = Problem97.CGN.vec2 (1 + a) b)
    (hcirc : a ^ 2 + b ^ 2 = r ^ 2)
    (hdot : a * Real.cos δ + b * Real.sin δ = r / 2)
    (hblo : b < 0) (hδlo : 0 < δ) (hδhi : δ < Real.pi / 3)
    (hcap : dist A q < dist A B) : False := by
  have hsin : 0 < Real.sin δ := by
    apply Real.sin_pos_of_pos_of_lt_pi hδlo
    have := Real.pi_pos; linarith
  have hcos : 0 < Real.cos δ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have := Real.pi_pos; linarith
    · have := Real.pi_pos; linarith
  have ha_pos : 0 < a := by
    have h1 : 0 < a * Real.cos δ := by nlinarith only [hr, hdot, hblo, hsin]
    rcases lt_trichotomy a 0 with h | h | h
    · nlinarith only [hr, hdot, hblo, hsin, hcos, h]
    · simp [h] at h1
    · exact h
  have hAB_sq : dist A B ^ 2 = 1 := by
    rw [hA, hB, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq]
    simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
  have hAq_sq : dist A q ^ 2 = 1 + 2 * a + r ^ 2 := by
    rw [hA, hq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq]
    simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    nlinarith only [hcirc]
  have h1 : 0 ≤ dist A q := dist_nonneg
  have h2 : 0 ≤ dist A B := dist_nonneg
  nlinarith only [ha_pos, hAB_sq, hAq_sq, hr, hcap, h1, h2]
abbrev PEqBLowerApexConfig
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (q : ℝ²) (r : ℝ) : Prop :=
  ∃ T : ℝ² → ℝ², ∃ _tau : Problem97.CGN.SimilarityTransportData T, ∃ δ a b : ℝ,
    T S.triangle.v1 = Problem97.CGN.vec2 0 0 ∧
    T S.triangle.v2 = Problem97.CGN.vec2 1 0 ∧
    T q = Problem97.CGN.vec2 (1 + a) b ∧
    0 < r ∧
    a ^ 2 + b ^ 2 = r ^ 2 ∧
    a * Real.cos δ + b * Real.sin δ = r / 2 ∧
    b < 0 ∧ 0 < δ ∧ δ < Real.pi / 3
theorem pEqB_row_impossible_of_normalized_config
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q : ℝ²} {r : ℝ}
    (hconfig : S.PEqBLowerApexConfig q r)
    (hcap : dist S.triangle.v1 q < dist S.triangle.v1 S.triangle.v2) :
    False := by
  rcases hconfig with ⟨T, tau, δ, a, b, hv1, hv2, hqT, hr, hcirc, hdot, hblo, hδlo, hδhi⟩
  have hcapT :
      dist (T S.triangle.v1) (T q) < dist (T S.triangle.v1) (T S.triangle.v2) := by
    rw [tau.dist_image, tau.dist_image]
    have hscale : 0 < tau.scale := tau.scale_pos
    nlinarith only [hcap, hscale, dist_nonneg (x := S.triangle.v1) (y := q), dist_nonneg (x := S.triangle.v1) (y := S.triangle.v2)]
  exact b3n9m051_pEqB_lower_apex_dist_contradiction
    (T S.triangle.v1) (T S.triangle.v2) (T q) r δ a b hr
    hv1 hv2 hqT hcirc hdot hblo hδlo hδhi hcapT
theorem pEqB_row_impossible_of_lower_witness
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q : ℝ²} {r : ℝ}
    (hqI3 : q ∈ S.I3)
    (hconfig : S.PEqBLowerApexConfig q r) :
    False :=
  S.pEqB_row_impossible_of_normalized_config hconfig (S.b3n9m051_v1_lt_v1v2_of_mem_I3 hqI3)
set_option maxHeartbeats 8000000 in
theorem pEqB_lower_apex_config_of_equilateral
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q : ℝ²}
    (hqI3 : q ∈ S.I3)
    (hBq : dist S.triangle.v2 q = dist S.triangle.v2 S.triangle.v3)
    (hDq : dist S.triangle.v3 q = dist S.triangle.v2 S.triangle.v3)
    (hsmall : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v1 S.triangle.v2)
    (hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3) :
    ∃ r : ℝ, S.PEqBLowerApexConfig q r := by
  classical
  let q1 : ℝ² := S.triangle.v1
  let q2 : ℝ² := S.triangle.v2
  let q3 : ℝ² := S.triangle.v3
  have hq1ne : q1 ≠ q2 := by simpa [q1, q2] using S.triangle.v12_ne
  rcases b3n9m051_exists_base_transportData q1 q2 hq1ne with
    ⟨Tbase, tauBase, hv1Base, hv2Base⟩
  have horientBase_ne : tauBase.orientation ≠ 0 := by
    intro h0
    have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tauBase.orientation_sq
    norm_num at this
  have hq3_base_nonzero : (Tbase q3) 1 ≠ 0 := by
    have hq3_sa_ne : signedArea2 q3 q1 q2 ≠ 0 := by
      have hv1O : ‖q1 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q1] using S.Packet.moser_on_boundary_1
      have hv2O : ‖q2 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q2] using S.Packet.moser_on_boundary_2
      have hv3O : ‖q3 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q3] using S.Packet.moser_on_boundary_3
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        hv3O hv1O hv2O
        S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
    have himg_ne : signedArea2 (Tbase q3) (Tbase q1) (Tbase q2) ≠ 0 := by
      rw [tauBase.halfplane_sign q3 q1 q2]
      exact mul_ne_zero
        (mul_ne_zero horientBase_ne (pow_ne_zero 2 (ne_of_gt tauBase.scale_pos)))
        hq3_sa_ne
    intro h0
    apply himg_ne
    rw [hv1Base, hv2Base, b3n9m051_signedArea2_baseChord_vec2]
    linarith
  have build_from :
      ∀ {T0 : ℝ² → ℝ²},
        (tau0 : Problem97.CGN.SimilarityTransportData T0) →
        T0 q1 = Problem97.CGN.vec2 (-1) 0 →
        T0 q2 = Problem97.CGN.vec2 1 0 →
        0 < (T0 q3) 1 →
        ∃ r : ℝ, S.PEqBLowerApexConfig q r := by
    intro T0 tau0 hv1 hv2 hq3y_pos
    let T : ℝ² → ℝ² := fun x => b3n9m051_halfShift (T0 x)
    let tau : Problem97.CGN.SimilarityTransportData T :=
      b3n9m051_similarityTransportComp tau0 b3n9m051_halfShiftSimilarityTransportData
    have hv1T : T q1 = Problem97.CGN.vec2 0 0 := by
      dsimp [T]; rw [hv1]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2T : T q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [T]; rw [hv2]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3y_T : 0 < (T q3) 1 := by
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (0 : ℝ) < (T0 q3) 1 / 2 := by linarith
      simpa using this
    have hqy_T : (T q) 1 < 0 := by
      have hxA : q ∈ A := S.CP.C3_subset (by
        unfold Problem97.FiniteEndpointShell.I3 at hqI3
        exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3))
      have hqC3 : q ∈ S.CP.C3 := by
        unfold Problem97.FiniteEndpointShell.I3 at hqI3
        exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3)
      have hq_ne_v1 : q ≠ q1 := by
        unfold Problem97.FiniteEndpointShell.I3 at hqI3
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqI3).2).1
      have hq_ne_v2 : q ≠ q2 := by
        unfold Problem97.FiniteEndpointShell.I3 at hqI3
        exact (Finset.mem_erase.mp hqI3).1
      have hq3_base_ne : signedArea2 q3 q1 q2 ≠ 0 := by
        have hv1O : dist q3 S.Packet.center = S.Packet.radius := by
          simpa [q3, dist_eq_norm] using S.Packet.moser_on_boundary_3
        have hv2O : dist q1 S.Packet.center = S.Packet.radius := by
          simpa [q1, dist_eq_norm] using S.Packet.moser_on_boundary_1
        have hv3O : dist q2 S.Packet.center = S.Packet.radius := by
          simpa [q2, dist_eq_norm] using S.Packet.moser_on_boundary_2
        exact MEC.signedArea2_ne_zero_of_three_dist_eq
          hv1O hv2O hv3O
          S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
      have hq_arc :
          signedArea2 q q1 q2 * signedArea2 q3 q1 q2 ≤ 0 := by
        exact (S.CP.arc_membership q hxA).2.2.1 hqC3
      have hq_base_ne : signedArea2 q q1 q2 ≠ 0 := by
        intro hz
        have hcol : Collinear ℝ ({q, q1, q2} : Set ℝ²) :=
          (Problem97.signedArea2_eq_zero_iff_collinear q q1 q2).1 hz
        exact False.elim <|
          (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) hxA S.triangle.v1_mem S.triangle.v2_mem
            hq_ne_v1 hq_ne_v2 S.triangle.v12_ne hcol
      have hq3_img_pos : 0 < signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
        rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2]; linarith
      have himg_nonpos :
          signedArea2 (T0 q) (T0 q1) (T0 q2) *
            signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 := by
        rw [tau0.halfplane_sign q q1 q2, tau0.halfplane_sign q3 q1 q2]
        have hrew :
            (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q q1 q2) *
                (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q3 q1 q2) =
              (tau0.orientation ^ 2) * (tau0.scale ^ 2 * tau0.scale ^ 2) *
                (signedArea2 q q1 q2 * signedArea2 q3 q1 q2) := by ring
        rw [hrew, tau0.orientation_sq]
        have hscale_nonneg : 0 ≤ tau0.scale ^ 2 * tau0.scale ^ 2 := by positivity
        simpa using mul_nonpos_of_nonneg_of_nonpos hscale_nonneg hq_arc
      have hq_img_lt : signedArea2 (T0 q) (T0 q1) (T0 q2) < 0 := by
        have hq_img_le : signedArea2 (T0 q) (T0 q1) (T0 q2) ≤ 0 := by
          by_contra hq_pos
          have : 0 < signedArea2 (T0 q) (T0 q1) (T0 q2) *
              signedArea2 (T0 q3) (T0 q1) (T0 q2) :=
            mul_pos (by linarith) hq3_img_pos
          linarith
        have hq_img_ne : signedArea2 (T0 q) (T0 q1) (T0 q2) ≠ 0 := by
          rw [tau0.halfplane_sign q q1 q2]
          have horient_ne : tau0.orientation ≠ 0 := by
            intro h0
            have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tau0.orientation_sq
            norm_num at this
          exact mul_ne_zero
            (mul_ne_zero horient_ne (pow_ne_zero 2 (ne_of_gt tau0.scale_pos))) hq_base_ne
        exact lt_of_le_of_ne hq_img_le hq_img_ne
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2] at hq_img_lt
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (T0 q) 1 / 2 < 0 := by linarith
      simpa using this
    have hq_ne_v2 : q ≠ q2 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp hqI3).1
    have hv3_ne_v2 : q3 ≠ q2 := by simpa [q2, q3] using S.triangle.v23_ne.symm
    set r : ℝ := dist (T q2) (T q) with hr_def
    have hd_q : 0 < dist q2 q := by
      rw [dist_pos]; exact fun h => hq_ne_v2 h.symm
    have hr_pos : 0 < r := by
      rw [hr_def, tau.dist_image]
      exact mul_pos tau.scale_pos hd_q
    have hBq_T : dist (T q2) (T q) = r := hr_def.symm
    have hBD_T : dist (T q2) (T q3) = r := by
      rw [hr_def, tau.dist_image, tau.dist_image]
      congr 1
      simpa [q2, q3] using hBq.symm
    have hDq_T : dist (T q3) (T q) = r := by
      rw [hr_def, tau.dist_image, tau.dist_image]
      congr 1
      calc dist q3 q = dist q2 q3 := by simpa [q2, q3] using hDq
        _ = dist q2 q := by simpa [q2, q3] using hBq.symm
    have hv2c0 : (T q2) 0 = 1 := by rw [hv2T]; simp [Problem97.CGN.vec2]
    have hv2c1 : (T q2) 1 = 0 := by rw [hv2T]; simp [Problem97.CGN.vec2]
    have hv1c0 : (T q1) 0 = 0 := by rw [hv1T]; simp [Problem97.CGN.vec2]
    have hv1c1 : (T q1) 1 = 0 := by rw [hv1T]; simp [Problem97.CGN.vec2]
    set dx : ℝ := (T q3) 0 - 1 with hdx_def
    set dy : ℝ := (T q3) 1 with hdy_def
    set a : ℝ := (T q) 0 - 1 with ha_def
    set b : ℝ := (T q) 1 with hb_def
    have hdy_pos : 0 < dy := by rw [hdy_def]; exact hq3y_T
    have hb_neg : b < 0 := by rw [hb_def]; exact hqy_T
    have hcircD : dx ^ 2 + dy ^ 2 = r ^ 2 := by
      have hsq := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T q2) (T q3)
      rw [hBD_T, hv2c0, hv2c1] at hsq
      rw [hdx_def, hdy_def]; nlinarith only [hsq]
    have hcircQ : a ^ 2 + b ^ 2 = r ^ 2 := by
      have hsq := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T q2) (T q)
      rw [hBq_T, hv2c0, hv2c1] at hsq
      rw [ha_def, hb_def]; nlinarith only [hsq]
    have hdot_raw : a * dx + b * dy = r ^ 2 / 2 := by
      have hsq := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T q3) (T q)
      rw [hDq_T] at hsq
      rw [ha_def, hb_def, hdx_def, hdy_def]
      nlinarith only [hcircD, hcircQ, hsq]
    have hlong_T : (1 : ℝ) < 1 + 2 * dx + r ^ 2 := by
      have hAB_T : dist (T q1) (T q2) = r * 0 + 1 := by
        rw [hv1T, hv2T, dist_eq_norm]
        have hvec :
            Problem97.CGN.vec2 0 0 - Problem97.CGN.vec2 1 0 =
              Problem97.CGN.vec2 (-1) 0 := by
          ext i <;> fin_cases i <;>
            simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
        rw [hvec, EuclideanSpace.norm_eq]
        norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have hAD :
          dist (T q1) (T q2) < dist (T q1) (T q3) := by
        rw [tau.dist_image, tau.dist_image]
        have hscale : 0 < tau.scale := tau.scale_pos
        have : dist q1 q2 < dist q1 q3 := by simpa [q1, q2, q3] using hlong
        nlinarith only [hlong, hscale, this, dist_nonneg (x := q1) (y := q2)]
      have hAB1 : dist (T q1) (T q2) = 1 := by rw [hAB_T]; ring
      have hAD_sq := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T q1) (T q3)
      rw [hv1c0, hv1c1] at hAD_sq
      have hAD_sq' : dist (T q1) (T q3) ^ 2 = 1 + 2 * dx + r ^ 2 := by
        rw [hAD_sq]; nlinarith only [hcircD, hdx_def, hdy_def]
      have hAD' : (1 : ℝ) < dist (T q1) (T q3) := by rw [hAB1] at hAD; exact hAD
      nlinarith only [hcircD, hAB_T, hAD, hAD_sq, hAD', hAD_sq', dist_nonneg (x := T q1) (y := T q3)]
    have hr_lt_one : r < 1 := by
      have hBD : dist (T q2) (T q3) < dist (T q1) (T q2) := by
        rw [tau.dist_image, tau.dist_image]
        have hscale : 0 < tau.scale := tau.scale_pos
        have : dist q2 q3 < dist q1 q2 := by simpa [q1, q2, q3] using hsmall
        nlinarith only [hsmall, hscale, this, dist_nonneg (x := q1) (y := q2)]
      have hAB1 : dist (T q1) (T q2) = 1 := by
        rw [hv1T, hv2T, dist_eq_norm]
        have hvec :
            Problem97.CGN.vec2 0 0 - Problem97.CGN.vec2 1 0 =
              Problem97.CGN.vec2 (-1) 0 := by
          ext i <;> fin_cases i <;>
            simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
        rw [hvec, EuclideanSpace.norm_eq]
        norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
      rw [hBD_T, hAB1] at hBD; exact hBD
    have hadx_big : r ^ 2 / 2 < a * dx := by
      have hbdy_neg : b * dy < 0 := mul_neg_of_neg_of_pos hb_neg hdy_pos
      linarith [hdot_raw]
    have ha_le : a ≤ r := by nlinarith only [hcircQ, hr_pos, sq_nonneg b]
    have ha_ge : -r ≤ a := by nlinarith only [hcircQ, hqy_T, ha_le, sq_nonneg b, hr_pos]
    have hdx_lb : -(r ^ 2) / 2 < dx := by nlinarith only [hlong_T]
    have hdx_gt : r / 2 < dx := by
      have ha_pos : 0 < a := by
        by_contra hanot
        have ha0 : a ≤ 0 := le_of_not_gt hanot
        have hdx_neg : dx < 0 := by
          rcases lt_trichotomy dx 0 with h | h | h
          · exact h
          · exfalso; rw [h, mul_zero] at hadx_big; nlinarith only [hadx_big, hr_pos, mul_pos hr_pos hr_pos]
          · exfalso
            have : a * dx ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 (le_of_lt h)
            nlinarith only [hadx_big, this, mul_pos hr_pos hr_pos]
        have hbound : a * dx ≤ -r * dx := by nlinarith only [hdot_raw, hr_lt_one, ha_ge, hq3y_T, hqy_T, hlong_T, hanot, hdx_neg]
        have hdx_lt : dx < -(r / 2) := by
          have : r ^ 2 / 2 < -r * dx := lt_of_lt_of_le hadx_big hbound
          nlinarith only [hadx_big, hbound, hr_lt_one, hr_pos, hlong_T, this]
        nlinarith only [hadx_big, hbound, hr_lt_one, hr_pos, hlong_T, hdx_lt, hdx_lb, mul_pos hr_pos hr_pos]
      have hdx_pos : 0 < dx := by
        by_contra hdxnot
        have hdx0 : dx ≤ 0 := le_of_not_gt hdxnot
        have : a * dx ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha_pos) hdx0
        nlinarith only [hlong_T, hadx_big, hdxnot, this, mul_pos hr_pos hr_pos]
      have hrdx : a * dx ≤ r * dx := by nlinarith only [hr_pos, hr_lt_one, ha_le, hdx_pos]
      nlinarith only [hr_pos, hadx_big, hrdx]
    have hcos_le : dx / r ≤ 1 := by
      rw [div_le_one hr_pos]
      nlinarith only [hcircD, hr_pos, hdy_pos, sq_nonneg (dx - r), mul_pos hr_pos hr_pos]
    have hcos_ge : -1 ≤ dx / r := by
      rw [le_div_iff₀ hr_pos]
      nlinarith only [hr_pos, hdx_gt, hcircD, hdy_pos, sq_nonneg (dx + r), mul_pos hr_pos hr_pos]
    set δ : ℝ := Real.arccos (dx / r) with hδ_def
    have hcosδ : Real.cos δ = dx / r := by
      rw [hδ_def, Real.cos_arccos hcos_ge hcos_le]
    have hsinδ : Real.sin δ = dy / r := by
      rw [hδ_def, Real.sin_arccos]
      have hsq : 1 - (dx / r) ^ 2 = (dy / r) ^ 2 := by
        field_simp
        nlinarith only [hcircD]
      rw [hsq, Real.sqrt_sq (by positivity)]
    have hδ_lo : 0 < δ := by
      rw [hδ_def]
      apply Real.arccos_pos.mpr
      rw [div_lt_one hr_pos]
      nlinarith only [hcircD, hr_pos, hq3y_T, hdx_gt, hdy_pos]
    have hδ_hi : δ < Real.pi / 3 := by
      have hcos_gt_half : (1 : ℝ) / 2 < Real.cos δ := by
        rw [hcosδ, lt_div_iff₀ hr_pos]; linarith [hdx_gt]
      have hcos_third : Real.cos (Real.pi / 3) = 1 / 2 := by
        rw [Real.cos_pi_div_three]
      by_contra hnot
      have hge : Real.pi / 3 ≤ δ := le_of_not_gt hnot
      have hδ_le_pi : δ ≤ Real.pi := by
        rw [hδ_def]; exact Real.arccos_le_pi _
      have hmono : Real.cos δ ≤ Real.cos (Real.pi / 3) := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        · positivity
        · exact hδ_le_pi
        · exact hge
      rw [hcos_third] at hmono
      linarith [hcos_gt_half, hmono]
    have hdot : a * Real.cos δ + b * Real.sin δ = r / 2 := by
      rw [hcosδ, hsinδ]
      have heq : a * (dx / r) + b * (dy / r) = (a * dx + b * dy) / r := by ring
      rw [heq, hdot_raw]
      field_simp
    have hqT : T q = Problem97.CGN.vec2 (1 + a) b := by
      rw [ha_def, hb_def]
      ext i <;> fin_cases i <;>
        simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    refine ⟨r, T, tau, δ, a, b, hv1T, hv2T, hqT, hr_pos, hcircQ, hdot, hb_neg, hδ_lo, hδ_hi⟩
  by_cases hq3pos : 0 < (Tbase q3) 1
  · exact build_from tauBase hv1Base hv2Base hq3pos
  · let Tflip : ℝ² → ℝ² := fun x => b3n9m051_flipY (Tbase x)
    let tauFlip : Problem97.CGN.SimilarityTransportData Tflip :=
      b3n9m051_similarityTransportComp tauBase b3n9m051_flipYSimilarityTransportData
    have hv1Flip : Tflip q1 = Problem97.CGN.vec2 (-1) 0 := by
      dsimp [Tflip]; rw [hv1Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2Flip : Tflip q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [Tflip]; rw [hv2Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3Flip : 0 < (Tflip q3) 1 := by
      dsimp [Tflip]
      simp only [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have hq3neg : (Tbase q3) 1 < 0 := by
        have hle : (Tbase q3) 1 ≤ 0 := le_of_not_gt hq3pos
        exact lt_of_le_of_ne hle hq3_base_nonzero
      simpa using hq3neg
    exact build_from tauFlip hv1Flip hv2Flip hq3Flip
theorem pEqB_row_impossible_of_equilateral
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q : ℝ²}
    (hqI3 : q ∈ S.I3)
    (hBq : dist S.triangle.v2 q = dist S.triangle.v2 S.triangle.v3)
    (hDq : dist S.triangle.v3 q = dist S.triangle.v2 S.triangle.v3)
    (hsmall : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v1 S.triangle.v2)
    (hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3) :
    False := by
  obtain ⟨r, hconfig⟩ :=
    S.pEqB_lower_apex_config_of_equilateral hqI3 hBq hDq hsmall hlong
  exact S.pEqB_row_impossible_of_lower_witness hqI3 hconfig
theorem b3n9m051_qEqC_reflection_below_contradiction
    (r θ δ : ℝ) (hr : 0 < r)
    (hcosθ : Real.cos θ = -(r / 2)) (hsinθ : 0 < Real.sin θ)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hcosδ : -(r / 2) < Real.cos δ) (hsinδ : 0 < Real.sin δ)
    (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi)
    (hqbelow : Real.sin (2 * δ - θ) < 0)
    (hAq : Real.cos (2 * δ - θ) < -(r / 2)) : False := by
  have hδpos : 0 < δ := by
    rcases lt_or_eq_of_le hδ0 with h | h
    · exact h
    · exfalso; rw [← h, Real.sin_zero] at hsinδ; exact lt_irrefl _ hsinδ
  have hδ_lt_θ : δ < θ := by
    rcases lt_trichotomy δ θ with hlt | heq | hgt
    · exact hlt
    · exfalso; rw [heq, hcosθ] at hcosδ; exact lt_irrefl _ hcosδ
    · exfalso
      have hcc := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0 hδπ hgt
      rw [hcosθ] at hcc
      linarith [hcc, hcosδ]
  set w : ℝ := 2 * δ - θ with hw_def
  have hw_lo : -Real.pi < w := by rw [hw_def]; linarith [hδpos, hθπ]
  have hw_hi : w < Real.pi := by rw [hw_def]; linarith [hδ_lt_θ, hθπ]
  have hw_neg : w < 0 := by
    by_contra hge
    push_neg at hge
    exact absurd (Real.sin_nonneg_of_nonneg_of_le_pi hge (le_of_lt hw_hi))
      (not_le.mpr hqbelow)
  have hneg_w_lo : 0 ≤ -w := by linarith [hw_neg]
  have hneg_w_lt : -w < θ := by rw [hw_def]; linarith [hδpos]
  have hcos_gt : Real.cos θ < Real.cos (-w) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hneg_w_lo hθπ hneg_w_lt
  rw [Real.cos_neg] at hcos_gt
  rw [hcosθ] at hcos_gt
  linarith [hAq, hcos_gt]
abbrev QEqCReflectionConfig
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (q : ℝ²) (r : ℝ) : Prop :=
  ∃ T : ℝ² → ℝ², ∃ _tau : Problem97.CGN.SimilarityTransportData T, ∃ θ δ : ℝ,
    T S.triangle.v1 = Problem97.CGN.vec2 0 0 ∧
    T S.triangle.v2 = Problem97.CGN.vec2 1 0 ∧
    0 < r ∧
    Real.cos θ = -(r / 2) ∧ 0 < Real.sin θ ∧ 0 ≤ θ ∧ θ ≤ Real.pi ∧
    -(r / 2) < Real.cos δ ∧ 0 < Real.sin δ ∧ 0 ≤ δ ∧ δ ≤ Real.pi ∧
    T q =
      Problem97.CGN.vec2
        (1 + r * Real.cos (2 * δ - θ)) (r * Real.sin (2 * δ - θ)) ∧
    Real.sin (2 * δ - θ) < 0
theorem qEqC_row_impossible_of_normalized_config
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q : ℝ²} {r : ℝ}
    (hconfig : S.QEqCReflectionConfig q r)
    (hcap : dist S.triangle.v1 q < dist S.triangle.v1 S.triangle.v2) :
    False := by
  rcases hconfig with
    ⟨T, tau, θ, δ, hv1, hv2, hr, hcosθ, hsinθ, hθ0, hθπ,
      hcosδ, hsinδ, hδ0, hδπ, hqT, hqbelow⟩
  have hcapT : dist (T S.triangle.v1) (T q) < dist (T S.triangle.v1) (T S.triangle.v2) := by
    rw [tau.dist_image, tau.dist_image]
    have hscale : 0 < tau.scale := tau.scale_pos
    nlinarith only [hcap, hscale, dist_nonneg (x := S.triangle.v1) (y := q), dist_nonneg (x := S.triangle.v1) (y := S.triangle.v2)]
  have hAB1 : dist (T S.triangle.v1) (T S.triangle.v2) = 1 := by
    rw [hv1, hv2, dist_eq_norm]
    have hvec :
        Problem97.CGN.vec2 0 0 - Problem97.CGN.vec2 1 0 = Problem97.CGN.vec2 (-1) 0 := by
      ext i <;> fin_cases i <;>
        simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    rw [hvec, EuclideanSpace.norm_eq]
    norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
  have hAq_sq : dist (T S.triangle.v1) (T q) ^ 2
      = 1 + 2 * r * Real.cos (2 * δ - θ) + r ^ 2 := by
    rw [hv1, hqT, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq]
    simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    nlinarith only [Real.sin_sq_add_cos_sq (2 * δ - θ)]
  have hAq : Real.cos (2 * δ - θ) < -(r / 2) := by
    rw [hAB1] at hcapT
    have hAq_nonneg : 0 ≤ dist (T S.triangle.v1) (T q) := dist_nonneg
    nlinarith only [hcapT, hAq_sq, hr, hAq_nonneg]
  exact b3n9m051_qEqC_reflection_below_contradiction r θ δ hr hcosθ hsinθ hθ0 hθπ
    hcosδ hsinδ hδ0 hδπ hqbelow hAq
theorem qEqC_row_impossible_of_lower_witness
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q : ℝ²} {r : ℝ}
    (hqI3 : q ∈ S.I3)
    (hconfig : S.QEqCReflectionConfig q r) :
    False :=
  S.qEqC_row_impossible_of_normalized_config hconfig (S.b3n9m051_v1_lt_v1v2_of_mem_I3 hqI3)
theorem b3n9m051_qEqC_reflection_coords
    (r cθ sθ cδ sδ cη sη : ℝ) (hr : 0 < r)
    (hcθ : cθ = -(r / 2)) (hsθ : 0 < sθ) (hθpyth : cθ ^ 2 + sθ ^ 2 = 1)
    (hcδ : -(r / 2) < cδ) (hsδ : 0 < sδ) (hδpyth : cδ ^ 2 + sδ ^ 2 = 1)
    (hηpyth : cη ^ 2 + sη ^ 2 = 1) (hsη : sη < 0)
    (hradical : cη * cδ + sη * sδ = cθ * cδ + sθ * sδ)
    (hne : ¬ (cη = cθ ∧ sη = sθ)) :
    ∃ θ δ : ℝ,
      Real.cos θ = cθ ∧ Real.sin θ = sθ ∧ 0 ≤ θ ∧ θ ≤ Real.pi ∧
      Real.cos δ = cδ ∧ Real.sin δ = sδ ∧ 0 ≤ δ ∧ δ ≤ Real.pi ∧
      cη = Real.cos (2 * δ - θ) ∧ sη = Real.sin (2 * δ - θ) := by
  have hcθ_mem : -1 ≤ cθ ∧ cθ ≤ 1 := by
    constructor <;> nlinarith [hθpyth, sq_nonneg sθ, sq_nonneg cθ]
  have hcδ_mem : -1 ≤ cδ ∧ cδ ≤ 1 := by
    constructor <;> nlinarith [hδpyth, sq_nonneg sδ, sq_nonneg cδ]
  have hcη_mem : -1 ≤ cη ∧ cη ≤ 1 := by
    constructor <;> nlinarith only [hηpyth, hsη, sq_nonneg sη, sq_nonneg cη]
  set θ : ℝ := Real.arccos cθ with hθ_def
  set δ : ℝ := Real.arccos cδ with hδ_def
  set η : ℝ := -Real.arccos cη with hη_def
  have hcosθ : Real.cos θ = cθ := Real.cos_arccos hcθ_mem.1 hcθ_mem.2
  have hsinθ : Real.sin θ = sθ := by
    rw [hθ_def, Real.sin_arccos]
    have : Real.sqrt (1 - cθ ^ 2) = Real.sqrt (sθ ^ 2) := by congr 1; nlinarith only [hθpyth]
    rw [this, Real.sqrt_sq (le_of_lt hsθ)]
  have hcosδ : Real.cos δ = cδ := Real.cos_arccos hcδ_mem.1 hcδ_mem.2
  have hsinδ : Real.sin δ = sδ := by
    rw [hδ_def, Real.sin_arccos]
    have : Real.sqrt (1 - cδ ^ 2) = Real.sqrt (sδ ^ 2) := by congr 1; nlinarith only [hδpyth]
    rw [this, Real.sqrt_sq (le_of_lt hsδ)]
  have hcosη : Real.cos η = cη := by
    rw [hη_def, Real.cos_neg]; exact Real.cos_arccos hcη_mem.1 hcη_mem.2
  have hsinη : Real.sin η = sη := by
    rw [hη_def, Real.sin_neg, Real.sin_arccos]
    have hsqrt : Real.sqrt (1 - cη ^ 2) = Real.sqrt (sη ^ 2) := by congr 1; nlinarith only [hηpyth]
    rw [hsqrt, Real.sqrt_sq_eq_abs, abs_of_neg hsη]; ring
  have hcoseq : Real.cos (η - δ) = Real.cos (θ - δ) := by
    rw [Real.cos_sub, Real.cos_sub, hcosη, hsinη, hcosθ, hsinθ, hcosδ, hsinδ]
    linarith [hradical]
  have hcoords : ¬ (Real.cos η = Real.cos θ ∧ Real.sin η = Real.sin θ) := by
    rw [hcosη, hsinη, hcosθ, hsinθ]; exact hne
  have hrefl : Real.cos η = Real.cos (2 * δ - θ) ∧ Real.sin η = Real.sin (2 * δ - θ) := by
    rw [Real.cos_eq_cos_iff] at hcoseq
    obtain ⟨k, hk | hk⟩ := hcoseq
    · exfalso; apply hcoords
      have he : η = θ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; linarith
      rw [he, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]; exact ⟨rfl, rfl⟩
    · have he : η = (2 * δ - θ) + ((k : ℤ) : ℝ) * (2 * Real.pi) := by linarith
      rw [he, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]; exact ⟨rfl, rfl⟩
  refine ⟨θ, δ, hcosθ, hsinθ, Real.arccos_nonneg cθ, Real.arccos_le_pi cθ,
    hcosδ, hsinδ, Real.arccos_nonneg cδ, Real.arccos_le_pi cδ, ?_, ?_⟩
  · rw [← hcosη, hrefl.1]
  · rw [← hsinη, hrefl.2]
set_option maxHeartbeats 8000000 in
theorem qEqC_reflection_config_of_shell
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q C : ℝ²}
    (hqI3 : q ∈ S.I3)
    (hAC : dist S.triangle.v1 C = dist S.triangle.v1 S.triangle.v2)
    (hBD : dist S.triangle.v2 S.triangle.v3 = dist S.triangle.v2 C)
    (hBq : dist S.triangle.v2 q = dist S.triangle.v2 C)
    (hDq : dist S.triangle.v3 q = dist S.triangle.v3 C)
    (hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3)
    (hCside :
      0 < signedArea2 C S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2)
    (hqC : q ≠ C) :
    ∃ r : ℝ, S.QEqCReflectionConfig q r := by
  classical
  let q1 : ℝ² := S.triangle.v1
  let q2 : ℝ² := S.triangle.v2
  let q3 : ℝ² := S.triangle.v3
  have hq1ne : q1 ≠ q2 := by simpa [q1, q2] using S.triangle.v12_ne
  rcases b3n9m051_exists_base_transportData q1 q2 hq1ne with
    ⟨Tbase, tauBase, hv1Base, hv2Base⟩
  have horientBase_ne : tauBase.orientation ≠ 0 := by
    intro h0
    have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tauBase.orientation_sq
    norm_num at this
  have hq3_base_nonzero : (Tbase q3) 1 ≠ 0 := by
    have hq3_sa_ne : signedArea2 q3 q1 q2 ≠ 0 := by
      have hv1O : ‖q1 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q1] using S.Packet.moser_on_boundary_1
      have hv2O : ‖q2 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q2] using S.Packet.moser_on_boundary_2
      have hv3O : ‖q3 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q3] using S.Packet.moser_on_boundary_3
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        hv3O hv1O hv2O
        S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
    have himg_ne : signedArea2 (Tbase q3) (Tbase q1) (Tbase q2) ≠ 0 := by
      rw [tauBase.halfplane_sign q3 q1 q2]
      exact mul_ne_zero
        (mul_ne_zero horientBase_ne (pow_ne_zero 2 (ne_of_gt tauBase.scale_pos)))
        hq3_sa_ne
    intro h0
    apply himg_ne
    rw [hv1Base, hv2Base, b3n9m051_signedArea2_baseChord_vec2]
    linarith
  have build_from :
      ∀ {T0 : ℝ² → ℝ²},
        (tau0 : Problem97.CGN.SimilarityTransportData T0) →
        T0 q1 = Problem97.CGN.vec2 (-1) 0 →
        T0 q2 = Problem97.CGN.vec2 1 0 →
        0 < (T0 q3) 1 →
        ∃ r : ℝ, S.QEqCReflectionConfig q r := by
    intro T0 tau0 hv1 hv2 hq3y_pos
    let T : ℝ² → ℝ² := fun x => b3n9m051_halfShift (T0 x)
    let tau : Problem97.CGN.SimilarityTransportData T :=
      b3n9m051_similarityTransportComp tau0 b3n9m051_halfShiftSimilarityTransportData
    have hv1T : T q1 = Problem97.CGN.vec2 0 0 := by
      dsimp [T]; rw [hv1]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2T : T q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [T]; rw [hv2]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3y_T : 0 < (T q3) 1 := by
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (0 : ℝ) < (T0 q3) 1 / 2 := by linarith
      simpa using this
    have hv2c0 : (T q2) 0 = 1 := by rw [hv2T]; simp [Problem97.CGN.vec2]
    have hv2c1 : (T q2) 1 = 0 := by rw [hv2T]; simp [Problem97.CGN.vec2]
    have hv1c0 : (T q1) 0 = 0 := by rw [hv1T]; simp [Problem97.CGN.vec2]
    have hv1c1 : (T q1) 1 = 0 := by rw [hv1T]; simp [Problem97.CGN.vec2]
    have hxA : q ∈ A := S.CP.C3_subset (by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3))
    have hqC3 : q ∈ S.CP.C3 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3)
    have hq_ne_v1 : q ≠ q1 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqI3).2).1
    have hq_ne_v2 : q ≠ q2 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp hqI3).1
    have hq3_base_ne : signedArea2 q3 q1 q2 ≠ 0 := by
      have hv1O : dist q3 S.Packet.center = S.Packet.radius := by
        simpa [q3, dist_eq_norm] using S.Packet.moser_on_boundary_3
      have hv2O : dist q1 S.Packet.center = S.Packet.radius := by
        simpa [q1, dist_eq_norm] using S.Packet.moser_on_boundary_1
      have hv3O : dist q2 S.Packet.center = S.Packet.radius := by
        simpa [q2, dist_eq_norm] using S.Packet.moser_on_boundary_2
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        hv1O hv2O hv3O
        S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
    have hq_arc : signedArea2 q q1 q2 * signedArea2 q3 q1 q2 ≤ 0 :=
      (S.CP.arc_membership q hxA).2.2.1 hqC3
    have hq_base_ne : signedArea2 q q1 q2 ≠ 0 := by
      intro hz
      have hcol : Collinear ℝ ({q, q1, q2} : Set ℝ²) :=
        (Problem97.signedArea2_eq_zero_iff_collinear q q1 q2).1 hz
      exact False.elim <|
        (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) hxA S.triangle.v1_mem S.triangle.v2_mem
          hq_ne_v1 hq_ne_v2 S.triangle.v12_ne hcol
    have hq3_img_pos : 0 < signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2]; linarith
    have hqy_T : (T q) 1 < 0 := by
      have himg_nonpos :
          signedArea2 (T0 q) (T0 q1) (T0 q2) * signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 := by
        rw [tau0.halfplane_sign q q1 q2, tau0.halfplane_sign q3 q1 q2]
        have hrew :
            (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q q1 q2) *
                (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q3 q1 q2) =
              (tau0.orientation ^ 2) * (tau0.scale ^ 2 * tau0.scale ^ 2) *
                (signedArea2 q q1 q2 * signedArea2 q3 q1 q2) := by ring
        rw [hrew, tau0.orientation_sq]
        have hscale_nonneg : 0 ≤ tau0.scale ^ 2 * tau0.scale ^ 2 := by positivity
        simpa using mul_nonpos_of_nonneg_of_nonpos hscale_nonneg hq_arc
      have hq_img_lt : signedArea2 (T0 q) (T0 q1) (T0 q2) < 0 := by
        have hq_img_le : signedArea2 (T0 q) (T0 q1) (T0 q2) ≤ 0 := by
          by_contra hq_pos
          have : 0 < signedArea2 (T0 q) (T0 q1) (T0 q2) *
              signedArea2 (T0 q3) (T0 q1) (T0 q2) := mul_pos (by linarith) hq3_img_pos
          linarith
        have hq_img_ne : signedArea2 (T0 q) (T0 q1) (T0 q2) ≠ 0 := by
          rw [tau0.halfplane_sign q q1 q2]
          have horient_ne : tau0.orientation ≠ 0 := by
            intro h0
            have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tau0.orientation_sq
            norm_num at this
          exact mul_ne_zero
            (mul_ne_zero horient_ne (pow_ne_zero 2 (ne_of_gt tau0.scale_pos))) hq_base_ne
        exact lt_of_le_of_ne hq_img_le hq_img_ne
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2] at hq_img_lt
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (T0 q) 1 / 2 < 0 := by linarith
      simpa using this
    have hC_base_ne : signedArea2 C q1 q2 ≠ 0 := by
      intro hz; rw [hz, zero_mul] at hCside; exact lt_irrefl _ hCside
    have hCy_T : 0 < (T C) 1 := by
      have hC_img_prod :
          0 < signedArea2 (T0 C) (T0 q1) (T0 q2) * signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
        rw [tau0.halfplane_sign C q1 q2, tau0.halfplane_sign q3 q1 q2]
        have hrew :
            (tau0.orientation * (tau0.scale ^ 2) * signedArea2 C q1 q2) *
                (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q3 q1 q2) =
              (tau0.orientation ^ 2) * (tau0.scale ^ 2 * tau0.scale ^ 2) *
                (signedArea2 C q1 q2 * signedArea2 q3 q1 q2) := by ring
        rw [hrew, tau0.orientation_sq]
        have hscale_pos : 0 < tau0.scale ^ 2 * tau0.scale ^ 2 := by
          have := tau0.scale_pos; positivity
        have hprod : 0 < signedArea2 C q1 q2 * signedArea2 q3 q1 q2 := by
          simpa [q1, q2, q3] using hCside
        have : 0 < tau0.scale ^ 2 * tau0.scale ^ 2 *
            (signedArea2 C q1 q2 * signedArea2 q3 q1 q2) := mul_pos hscale_pos hprod
        linarith [this]
      have hC_img_pos : 0 < signedArea2 (T0 C) (T0 q1) (T0 q2) := by
        by_contra hle
        push_neg at hle
        have : signedArea2 (T0 C) (T0 q1) (T0 q2) *
            signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hq3_img_pos)
        linarith
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2] at hC_img_pos
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (0 : ℝ) < (T0 C) 1 / 2 := by linarith
      simpa using this
    have hv3_ne_v2 : q3 ≠ q2 := by simpa [q2, q3] using S.triangle.v23_ne.symm
    set r : ℝ := dist (T q2) (T C) with hr_def
    have hC_ne_v2 : C ≠ q2 := by
      intro h; rw [h] at hC_base_ne
      exact hC_base_ne (by
        have : signedArea2 q2 q1 q2 = 0 := by
          simp [signedArea2]
        simpa [q1, q2] using this)
    have hd_C : 0 < dist q2 C := by rw [dist_pos]; exact fun h => hC_ne_v2 h.symm
    have hr_pos : 0 < r := by
      rw [hr_def, tau.dist_image]; exact mul_pos tau.scale_pos hd_C
    have hBC_T : dist (T q2) (T C) = r := hr_def.symm
    have hBq_T : dist (T q2) (T q) = r := by
      rw [hr_def, tau.dist_image, tau.dist_image]
      have : dist q2 q = dist q2 C := by simpa [q2] using hBq
      rw [this]
    have hBD_T : dist (T q2) (T q3) = r := by
      rw [hr_def, tau.dist_image, tau.dist_image]
      have : dist q2 q3 = dist q2 C := by simpa [q2, q3] using hBD
      rw [this]
    have hDq_T : dist (T q3) (T q) = dist (T q3) (T C) := by
      rw [tau.dist_image, tau.dist_image]
      have : dist q3 q = dist q3 C := by simpa [q3] using hDq
      rw [this]
    set cθ : ℝ := ((T C) 0 - 1) / r with hcθ_def
    set sθ : ℝ := (T C) 1 / r with hsθ_def
    set cδ : ℝ := ((T q3) 0 - 1) / r with hcδ_def
    set sδ : ℝ := (T q3) 1 / r with hsδ_def
    set cη : ℝ := ((T q) 0 - 1) / r with hcη_def
    set sη : ℝ := (T q) 1 / r with hsη_def
    have hθpyth : cθ ^ 2 + sθ ^ 2 = 1 := by
      have hsq := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T q2) (T C)
      rw [hBC_T, hv2c0, hv2c1] at hsq
      rw [hcθ_def, hsθ_def]; field_simp; nlinarith only [hsq]
    have hδpyth : cδ ^ 2 + sδ ^ 2 = 1 := by
      have hsq := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T q2) (T q3)
      rw [hBD_T, hv2c0, hv2c1] at hsq
      rw [hcδ_def, hsδ_def]; field_simp; nlinarith only [hsq]
    have hηpyth : cη ^ 2 + sη ^ 2 = 1 := by
      have hsq := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T q2) (T q)
      rw [hBq_T, hv2c0, hv2c1] at hsq
      rw [hcη_def, hsη_def]; field_simp; nlinarith only [hsq]
    have hsθ_pos : 0 < sθ := by rw [hsθ_def]; positivity
    have hsδ_pos : 0 < sδ := by rw [hsδ_def]; positivity
    have hsη_neg : sη < 0 := by
      rw [hsη_def]; exact div_neg_of_neg_of_pos hqy_T hr_pos
    have hAB1 : dist (T q1) (T q2) = 1 := by
      rw [hv1T, hv2T, dist_eq_norm]
      have hvec :
          Problem97.CGN.vec2 0 0 - Problem97.CGN.vec2 1 0 = Problem97.CGN.vec2 (-1) 0 := by
        ext i <;> fin_cases i <;>
          simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
      rw [hvec, EuclideanSpace.norm_eq]
      norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hAC_T : dist (T q1) (T C) = 1 := by
      rw [tau.dist_image]
      have : dist (T q1) (T q2) = tau.scale * dist q1 q2 := tau.dist_image q1 q2
      rw [hAB1] at this
      have hAC' : dist q1 C = dist q1 q2 := by simpa [q1, q2] using hAC
      rw [hAC']; linarith [this]
    have hcθ_eq : cθ = -(r / 2) := by
      have hACsq : (T C) 0 ^ 2 + (T C) 1 ^ 2 = 1 := by
        have h := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T q1) (T C)
        rw [hAC_T, hv1c0, hv1c1] at h
        nlinarith only [h]
      have hcirc : ((T C) 0 - 1) ^ 2 + (T C) 1 ^ 2 = r ^ 2 := by
        have h := hθpyth
        rw [hcθ_def, hsθ_def] at h
        field_simp at h
        nlinarith only [h]
      have hTC0 : (T C) 0 = 1 - r ^ 2 / 2 := by nlinarith only [hACsq, hcirc]
      rw [hcθ_def, hTC0]; field_simp; ring
    have hcδ_gt : -(r / 2) < cδ := by
      have hAD : 1 < dist (T q1) (T q3) := by
        rw [tau.dist_image]
        have hsc : dist (T q1) (T q2) = tau.scale * dist q1 q2 := tau.dist_image q1 q2
        rw [hAB1] at hsc
        have hlong' : dist q1 q2 < dist q1 q3 := by simpa [q1, q2, q3] using hlong
        nlinarith only [hsc, hlong, hlong', tau.scale_pos, dist_nonneg (x := q1) (y := q2)]
      have hADsq : 1 < (T q3) 0 ^ 2 + (T q3) 1 ^ 2 := by
        have h := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq (T q1) (T q3)
        rw [hv1c0, hv1c1] at h
        nlinarith only [hAD, h, dist_nonneg (x := T q1) (y := T q3)]
      have hBDsq : ((T q3) 0 - 1) ^ 2 + (T q3) 1 ^ 2 = r ^ 2 := by
        have h := hδpyth
        rw [hcδ_def, hsδ_def] at h
        field_simp at h
        nlinarith only [h]
      rw [hcδ_def, lt_div_iff₀ hr_pos]
      nlinarith only [hADsq, hBDsq]
    have hrne : r ≠ 0 := ne_of_gt hr_pos
    have hTC0 : (T C) 0 = 1 + r * cθ := by rw [hcθ_def]; field_simp; ring
    have hTC1 : (T C) 1 = r * sθ := by rw [hsθ_def]; field_simp
    have hTD0 : (T q3) 0 = 1 + r * cδ := by rw [hcδ_def]; field_simp; ring
    have hTD1 : (T q3) 1 = r * sδ := by rw [hsδ_def]; field_simp
    have hTq0 : (T q) 0 = 1 + r * cη := by rw [hcη_def]; field_simp; ring
    have hTq1 : (T q) 1 = r * sη := by rw [hsη_def]; field_simp
    have hradical : cη * cδ + sη * sδ = cθ * cδ + sθ * sδ := by
      have hsqeq : dist (T q3) (T q) ^ 2 = dist (T q3) (T C) ^ 2 := by rw [hDq_T]
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq] at hsqeq
      rw [hTC0, hTC1, hTD0, hTD1, hTq0, hTq1] at hsqeq
      have hrne : r ≠ 0 := ne_of_gt hr_pos
      have hkey : (cη * cδ + sη * sδ) * r ^ 2 = (cθ * cδ + sθ * sδ) * r ^ 2 := by
        nlinarith only [hsqeq, hθpyth, hηpyth, hδpyth]
      have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
      exact mul_right_cancel₀ (ne_of_gt hr2pos) hkey
    have hne : ¬ (cη = cθ ∧ sη = sθ) := by
      rintro ⟨hc, hs⟩
      apply hqC
      have h0 : (T q) 0 = (T C) 0 := by rw [hTq0, hTC0, hc]
      have h1 : (T q) 1 = (T C) 1 := by rw [hTq1, hTC1, hs]
      have hTqC : T q = T C := by
        ext i; fin_cases i
        · exact h0
        · exact h1
      have hd0 : dist (T q) (T C) = 0 := by rw [hTqC]; simp
      rw [tau.dist_image] at hd0
      have : dist q C = 0 := by
        rcases mul_eq_zero.mp hd0 with h | h
        · exact absurd h (ne_of_gt tau.scale_pos)
        · exact h
      exact dist_eq_zero.mp this
    obtain ⟨θ, δ, hcosθ, hsinθ, hθ0, hθπ, hcosδ, hsinδ, hδ0, hδπ, hcη_eq, hsη_eq⟩ :=
      b3n9m051_qEqC_reflection_coords r cθ sθ cδ sδ cη sη hr_pos hcθ_eq hsθ_pos hθpyth
        hcδ_gt hsδ_pos hδpyth hηpyth hsη_neg hradical hne
    have hcosθ' : Real.cos θ = -(r / 2) := by rw [hcosθ]; exact hcθ_eq
    have hsinθ' : 0 < Real.sin θ := by rw [hsinθ]; exact hsθ_pos
    have hcosδ' : -(r / 2) < Real.cos δ := by rw [hcosδ]; exact hcδ_gt
    have hsinδ' : 0 < Real.sin δ := by rw [hsinδ]; exact hsδ_pos
    have hqbelow' : Real.sin (2 * δ - θ) < 0 := by rw [← hsη_eq]; exact hsη_neg
    have hTq0' : (T q) 0 = 1 + r * Real.cos (2 * δ - θ) := by rw [hTq0, hcη_eq]
    have hTq1' : (T q) 1 = r * Real.sin (2 * δ - θ) := by rw [hTq1, hsη_eq]
    have hqcoord : T q =
        Problem97.CGN.vec2 (1 + r * Real.cos (2 * δ - θ)) (r * Real.sin (2 * δ - θ)) := by
      ext i; fin_cases i
      · change (T q) 0 = _
        rw [hTq0']; simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
      · change (T q) 1 = _
        rw [hTq1']; simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    exact ⟨r, T, tau, θ, δ, hv1T, hv2T, hr_pos,
      hcosθ', hsinθ', hθ0, hθπ, hcosδ', hsinδ', hδ0, hδπ, hqcoord, hqbelow'⟩
  by_cases hq3pos : 0 < (Tbase q3) 1
  · exact build_from tauBase hv1Base hv2Base hq3pos
  · let Tflip : ℝ² → ℝ² := fun x => b3n9m051_flipY (Tbase x)
    let tauFlip : Problem97.CGN.SimilarityTransportData Tflip :=
      b3n9m051_similarityTransportComp tauBase b3n9m051_flipYSimilarityTransportData
    have hv1Flip : Tflip q1 = Problem97.CGN.vec2 (-1) 0 := by
      dsimp [Tflip]; rw [hv1Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2Flip : Tflip q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [Tflip]; rw [hv2Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3Flip : 0 < (Tflip q3) 1 := by
      dsimp [Tflip]
      simp only [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have hq3neg : (Tbase q3) 1 < 0 := by
        have hle : (Tbase q3) 1 ≤ 0 := le_of_not_gt hq3pos
        exact lt_of_le_of_ne hle hq3_base_nonzero
      simpa using hq3neg
    exact build_from tauFlip hv1Flip hv2Flip hq3Flip
theorem qEqC_row_impossible_of_reflection
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q C : ℝ²}
    (hqI3 : q ∈ S.I3)
    (hAC : dist S.triangle.v1 C = dist S.triangle.v1 S.triangle.v2)
    (hBD : dist S.triangle.v2 S.triangle.v3 = dist S.triangle.v2 C)
    (hBq : dist S.triangle.v2 q = dist S.triangle.v2 C)
    (hDq : dist S.triangle.v3 q = dist S.triangle.v3 C)
    (hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3)
    (hCside :
      0 < signedArea2 C S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2)
    (hqC : q ≠ C) :
    False := by
  obtain ⟨r, hconfig⟩ :=
    S.qEqC_reflection_config_of_shell hqI3 hAC hBD hBq hDq hlong hCside hqC
  exact S.qEqC_row_impossible_of_lower_witness hqI3 hconfig
theorem n4d_bA_2_q_eq_C_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hlower : FormBv1A2SelectorV2LowerPacket S Z r s)
    (hpacket3 : SelectorV3Qa2Packet S Z t) :
    False := by
  classical
  rcases hlower with ⟨hA2, ha2eq, hTcard, hI2sub, hC1eq, hC3eq⟩
  rcases hpacket3 with ⟨hI3sub, p, hp, hpeq, hqeqC2⟩
  let T := S.witnessClassAt_v2 s
  have hv3T : S.triangle.v3 ∈ T := by
    have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    rw [← hC1eq] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hq :
      (Z.a3 : ℝ²) ∈ T ∩ S.CP.C3 ∨ (Z.b3 : ℝ²) ∈ T ∩ S.CP.C3 := by
    rcases hC3eq with hqa3 | hqb3
    · left
      have hmem : Z.a3 ∈ ({Z.a3} : Finset ℝ²) := by simp
      rw [← hqa3] at hmem
      exact hmem
    · right
      have hmem : Z.b3 ∈ ({Z.b3} : Finset ℝ²) := by simp
      rw [← hqb3] at hmem
      exact hmem
  obtain ⟨q, hqI3, hqT2⟩ : ∃ q : ℝ², q ∈ S.I3 ∧ q ∈ T := by
    rcases hq with hqa3 | hqb3
    · refine ⟨Z.a3, ?_, ?_⟩
      · rw [Z.hI3]; simp
      · exact (Finset.mem_inter.mp hqa3).1
    · refine ⟨Z.b3, ?_, ?_⟩
      · rw [Z.hI3]; simp
      · exact (Finset.mem_inter.mp hqb3).1
  have hAC : dist S.triangle.v1 Z.a2 = dist S.triangle.v1 S.triangle.v2 := by
    have ha2T1 : Z.a2 ∈ S.witnessClassAt_v1 r := by
      have ha2mem : Z.a2 ∈ ({Z.a2} : Finset ℝ²) := by simp
      rw [← ha2eq] at ha2mem
      exact (Finset.mem_inter.mp ha2mem).1
    have hv2T1 : S.triangle.v2 ∈ S.witnessClassAt_v1 r := by
      rcases hB with ⟨x, hxI2, hxeq, hv2eq⟩
      have hv2mem : S.triangle.v2 ∈ ({S.triangle.v2} : Finset ℝ²) := by simp
      rw [← hv2eq] at hv2mem
      exact (Finset.mem_inter.mp hv2mem).1
    have ha2dist : dist S.triangle.v1 Z.a2 = r := by
      simpa using (Finset.mem_filter.mp ha2T1).2
    have hv2dist : dist S.triangle.v1 S.triangle.v2 = r := by
      simpa using (Finset.mem_filter.mp hv2T1).2
    rw [ha2dist, hv2dist]
  have ha2T2 : Z.a2 ∈ T := hI2sub hA2
  have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
    simpa using (Finset.mem_filter.mp hv3T).2
  have ha2rad2 : dist S.triangle.v2 Z.a2 = s := by
    simpa using (Finset.mem_filter.mp ha2T2).2
  have hBD : dist S.triangle.v2 S.triangle.v3 = dist S.triangle.v2 Z.a2 := by
    rw [hv3rad, ha2rad2]
  have hqrad2 : dist S.triangle.v2 q = s := by
    simpa using (Finset.mem_filter.mp hqT2).2
  have hBq : dist S.triangle.v2 q = dist S.triangle.v2 Z.a2 := by
    rw [hqrad2, ha2rad2]
  have ha2T3 : Z.a2 ∈ S.witnessClassAt_v3 t := by
    have ha2mem : Z.a2 ∈ ({Z.a2} : Finset ℝ²) := by simp
    rw [← hqeqC2] at ha2mem
    exact (Finset.mem_inter.mp ha2mem).1
  have hqT3 : q ∈ S.witnessClassAt_v3 t := hI3sub hqI3
  have ha2rad3 : dist S.triangle.v3 Z.a2 = t := by
    simpa using (Finset.mem_filter.mp ha2T3).2
  have hqrad3 : dist S.triangle.v3 q = t := by
    simpa using (Finset.mem_filter.mp hqT3).2
  have hDq : dist S.triangle.v3 q = dist S.triangle.v3 Z.a2 := by
    rw [hqrad3, ha2rad3]
  have hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3 := by
    have h := S.b3n9m051_v1_lt_v1v3_of_mem_I2 (p := Z.a2) hA2
    rwa [hAC] at h
  have hCside :
      0 < signedArea2 Z.a2 S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 :=
    (b3n9m051_coreSupport S).c2_vertex_same_open_side_as_v3 hA2
  have hqC : q ≠ Z.a2 := by
    intro hqa2
    have hlt := S.b3n9m051_v1_lt_v1v2_of_mem_I3 hqI3
    rw [hqa2, ← hAC] at hlt
    exact lt_irrefl _ hlt
  exact S.qEqC_row_impossible_of_reflection hqI3 hAC hBD hBq hDq hlong hCside hqC
theorem qEqE_row_impossible_of_reflection
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q E : ℝ²}
    (hqI3 : q ∈ S.I3)
    (hAE : dist S.triangle.v1 E = dist S.triangle.v1 S.triangle.v2)
    (hBD : dist S.triangle.v2 S.triangle.v3 = dist S.triangle.v2 E)
    (hBq : dist S.triangle.v2 q = dist S.triangle.v2 E)
    (hDq : dist S.triangle.v3 q = dist S.triangle.v3 E)
    (hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3)
    (hEside :
      0 < signedArea2 E S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2)
    (hqE : q ≠ E) :
    False :=
  S.qEqC_row_impossible_of_reflection hqI3 hAE hBD hBq hDq hlong hEside hqE
theorem b3n9m051_qEqE_reflection_coords
    (r cε sε cδ sδ cη sη : ℝ)
    (hsε : 0 < sε) (hεpyth : cε ^ 2 + sε ^ 2 = 1)
    (hsδ : 0 < sδ) (hδpyth : cδ ^ 2 + sδ ^ 2 = 1)
    (hηpyth : cη ^ 2 + sη ^ 2 = 1) (hsη : sη < 0)
    (hradical : cη * cδ + sη * sδ = cε * cδ + sε * sδ)
    (hne : ¬ (cη = cε ∧ sη = sε)) :
    ∃ ε δ : ℝ,
      Real.cos ε = cε ∧ Real.sin ε = sε ∧ 0 ≤ ε ∧ ε ≤ Real.pi ∧
      Real.cos δ = cδ ∧ Real.sin δ = sδ ∧ 0 ≤ δ ∧ δ ≤ Real.pi ∧
      cη = Real.cos (2 * δ - ε) ∧ sη = Real.sin (2 * δ - ε) := by
  have hcε_mem : -1 ≤ cε ∧ cε ≤ 1 := by
    constructor <;> nlinarith only [hεpyth, hsε, sq_nonneg sε, sq_nonneg cε]
  have hcδ_mem : -1 ≤ cδ ∧ cδ ≤ 1 := by
    constructor <;> nlinarith only [hδpyth, hsδ, sq_nonneg sδ, sq_nonneg cδ]
  have hcη_mem : -1 ≤ cη ∧ cη ≤ 1 := by
    constructor <;> nlinarith only [hηpyth, hsη, sq_nonneg sη, sq_nonneg cη]
  set ε : ℝ := Real.arccos cε with hε_def
  set δ : ℝ := Real.arccos cδ with hδ_def
  set η : ℝ := -Real.arccos cη with hη_def
  have hcosε : Real.cos ε = cε := Real.cos_arccos hcε_mem.1 hcε_mem.2
  have hsinε : Real.sin ε = sε := by
    rw [hε_def, Real.sin_arccos]
    have : Real.sqrt (1 - cε ^ 2) = Real.sqrt (sε ^ 2) := by congr 1; nlinarith only [hεpyth]
    rw [this, Real.sqrt_sq (le_of_lt hsε)]
  have hcosδ : Real.cos δ = cδ := Real.cos_arccos hcδ_mem.1 hcδ_mem.2
  have hsinδ : Real.sin δ = sδ := by
    rw [hδ_def, Real.sin_arccos]
    have : Real.sqrt (1 - cδ ^ 2) = Real.sqrt (sδ ^ 2) := by congr 1; nlinarith only [hδpyth]
    rw [this, Real.sqrt_sq (le_of_lt hsδ)]
  have hcosη : Real.cos η = cη := by
    rw [hη_def, Real.cos_neg]; exact Real.cos_arccos hcη_mem.1 hcη_mem.2
  have hsinη : Real.sin η = sη := by
    rw [hη_def, Real.sin_neg, Real.sin_arccos]
    have hsqrt : Real.sqrt (1 - cη ^ 2) = Real.sqrt (sη ^ 2) := by congr 1; nlinarith only [hηpyth]
    rw [hsqrt, Real.sqrt_sq_eq_abs, abs_of_neg hsη]; ring
  have hcoseq : Real.cos (η - δ) = Real.cos (ε - δ) := by
    rw [Real.cos_sub, Real.cos_sub, hcosη, hsinη, hcosε, hsinε, hcosδ, hsinδ]
    linarith [hradical]
  have hcoords : ¬ (Real.cos η = Real.cos ε ∧ Real.sin η = Real.sin ε) := by
    rw [hcosη, hsinη, hcosε, hsinε]; exact hne
  have hrefl : Real.cos η = Real.cos (2 * δ - ε) ∧ Real.sin η = Real.sin (2 * δ - ε) := by
    rw [Real.cos_eq_cos_iff] at hcoseq
    obtain ⟨k, hk | hk⟩ := hcoseq
    · exfalso; apply hcoords
      have he : η = ε + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; linarith
      rw [he, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]; exact ⟨rfl, rfl⟩
    · have he : η = (2 * δ - ε) + ((k : ℤ) : ℝ) * (2 * Real.pi) := by linarith
      rw [he, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]; exact ⟨rfl, rfl⟩
  refine ⟨ε, δ, hcosε, hsinε, Real.arccos_nonneg cε, Real.arccos_le_pi cε,
    hcosδ, hsinδ, Real.arccos_nonneg cδ, Real.arccos_le_pi cδ, ?_, ?_⟩
  · rw [← hcosη, hrefl.1]
  · rw [← hsinη, hrefl.2]
theorem b3n9m051_qEqE_param_t (r S cd sd Sx Sy : ℝ) (hr : 0 < r) (hS : 0 < S)
    (hcirc : (Sx - (1 + r * cd)) ^ 2 + (Sy - r * sd) ^ 2 = (r * S) ^ 2) :
    ∃ t : ℝ, Sx = 1 + r * cd + r * S * Real.cos t ∧ Sy = r * sd + r * S * Real.sin t := by
  set ct := (Sx - (1 + r * cd)) / (r * S) with hct
  set st := (Sy - r * sd) / (r * S) with hst
  have hrS : 0 < r * S := mul_pos hr hS
  have hrSne : r * S ≠ 0 := ne_of_gt hrS
  have hpyth : ct ^ 2 + st ^ 2 = 1 := by rw [hct, hst]; field_simp; nlinarith only [hcirc]
  have hcx : r * S * ct = Sx - (1 + r * cd) := by rw [hct]; field_simp
  have hsy : r * S * st = Sy - r * sd := by rw [hst]; field_simp
  by_cases hsnn : 0 ≤ st
  · refine ⟨Real.arccos ct, ?_, ?_⟩
    · rw [Real.cos_arccos (by nlinarith only [hpyth, sq_nonneg st]) (by nlinarith only [hpyth, sq_nonneg st])]
      linarith [hcx]
    · rw [Real.sin_arccos]
      have : Real.sqrt (1 - ct ^ 2) = Real.sqrt (st ^ 2) := by congr 1; nlinarith only [hpyth]
      rw [this, Real.sqrt_sq hsnn]; linarith [hsy]
  · push_neg at hsnn
    refine ⟨-Real.arccos ct, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos (by nlinarith only [hpyth, sq_nonneg st]) (by nlinarith only [hpyth, sq_nonneg st])]
      linarith [hcx]
    · rw [Real.sin_neg, Real.sin_arccos]
      have : Real.sqrt (1 - ct ^ 2) = Real.sqrt (st ^ 2) := by congr 1; nlinarith only [hpyth]
      rw [this, Real.sqrt_sq_eq_abs, abs_of_neg hsnn]
      have hneg : r * S * (-st) = -(Sy - r * sd) := by rw [← hsy]; ring
      linarith [hneg]
set_option maxHeartbeats 800000 in
lemma b3n9m051_sign_pin_lower_bound (r x0 x1 : ℝ) (hr : 0 < r)
    (hpyth : ((x0 - 1) / r) ^ 2 + (x1 / r) ^ 2 = 1)
    (hbig : 1 < x0 ^ 2 + x1 ^ 2) :
    -(r / 2) < (x0 - 1) / r := by
  have hcirc : (x0 - 1) ^ 2 + x1 ^ 2 = r ^ 2 := by
    field_simp at hpyth; nlinarith only [hpyth]
  rw [lt_div_iff₀ hr]
  nlinarith only [hbig, hcirc, sq_nonneg x1]
set_option maxHeartbeats 800000 in
lemma b3n9m051_sign_pin_upper_bound (r x0 x1 : ℝ) (hr : 0 < r)
    (hpyth : ((x0 - 1) / r) ^ 2 + (x1 / r) ^ 2 = 1)
    (hsmall : x0 ^ 2 + x1 ^ 2 < 1) :
    (x0 - 1) / r < -(r / 2) := by
  have hcirc : (x0 - 1) ^ 2 + x1 ^ 2 = r ^ 2 := by
    field_simp at hpyth; nlinarith only [hpyth]
  rw [div_lt_iff₀ hr]
  nlinarith only [hsmall, hcirc, sq_nonneg x1]
set_option maxHeartbeats 800000 in
lemma b3n9m051_chord_sq_formula (r : ℝ) (hr : 0 < r) (δ ε : ℝ) :
    (2 - 2 * Real.cos (δ - ε)) =
        ((1 + r * Real.cos δ - (1 + r * Real.cos ε)) ^ 2
          + (r * Real.sin δ - r * Real.sin ε) ^ 2) / r ^ 2 := by
  rw [Real.cos_sub]
  have hpd : Real.sin δ ^ 2 + Real.cos δ ^ 2 = 1 := Real.sin_sq_add_cos_sq δ
  have hpe : Real.sin ε ^ 2 + Real.cos ε ^ 2 = 1 := Real.sin_sq_add_cos_sq ε
  field_simp
  nlinarith only [hpd, hpe]
set_option maxHeartbeats 400000 in
lemma b3n9m051_circle_pyth (p q2 : ℝ²) (r : ℝ) (hrne : r ≠ 0)
    (hq20 : q2 0 = 1) (hq21 : q2 1 = 0)
    (hdist : dist q2 p = r) :
    ((p 0 - 1) / r) ^ 2 + (p 1 / r) ^ 2 = 1 := by
  have hsq := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq q2 p
  rw [hq20, hq21, hdist] at hsq
  field_simp
  nlinarith only [hsq]
set_option maxHeartbeats 400000 in
lemma b3n9m051_normsq_lt_of_origin_dist_lt (p q1 : ℝ²)
    (hq10 : q1 0 = 0) (hq11 : q1 1 = 0)
    (h : dist q1 p < 1) :
    p 0 ^ 2 + p 1 ^ 2 < 1 := by
  have hh := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq q1 p
  rw [hq10, hq11] at hh; simp only [zero_sub, neg_sq] at hh
  nlinarith only [h, hh, dist_nonneg (x := q1) (y := p)]
set_option maxHeartbeats 400000 in
lemma b3n9m051_normsq_gt_of_origin_dist_gt (p q1 : ℝ²)
    (hq10 : q1 0 = 0) (hq11 : q1 1 = 0)
    (h : 1 < dist q1 p) :
    1 < p 0 ^ 2 + p 1 ^ 2 := by
  have hh := b3n9m051_dist_sq_eq_coord_sq_add_coord_sq q1 p
  rw [hq10, hq11] at hh; simp only [zero_sub, neg_sq] at hh
  nlinarith only [h, hh, dist_nonneg (x := q1) (y := p)]
set_option maxHeartbeats 400000 in
lemma b3n9m051_dist_eq_r_sqrt_of_sq (distDq r : ℝ) (hr : 0 < r) (δ ε : ℝ)
    (hgeq : 0 ≤ distDq)
    (heqsq : distDq ^ 2 = r ^ 2 * (2 - 2 * Real.cos (δ - ε))) :
    distDq = r * Real.sqrt (2 - 2 * Real.cos (δ - ε)) := by
  have hnn : 0 ≤ 2 - 2 * Real.cos (δ - ε) := by nlinarith only [Real.cos_le_one (δ - ε)]
  have hrS_nn : 0 ≤ r * Real.sqrt (2 - 2 * Real.cos (δ - ε)) :=
    mul_nonneg (le_of_lt hr) (Real.sqrt_nonneg _)
  have heqsq2 : distDq ^ 2 = (r * Real.sqrt (2 - 2 * Real.cos (δ - ε))) ^ 2 := by
    rw [heqsq, mul_pow, Real.sq_sqrt hnn]
  nlinarith only [heqsq2, hgeq, hrS_nn, sq_nonneg (distDq - r * Real.sqrt (2 - 2 * Real.cos (δ - ε)))]
set_option maxHeartbeats 8000000 in
theorem qEqE_lowerArc_sameSign_of_shell
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q qs E : ℝ²}
    (hqI3 : q ∈ S.I3) (hqsI3 : qs ∈ S.I3)
    (hDqs : dist S.triangle.v3 qs = dist S.triangle.v3 q)
    (hBq : dist S.triangle.v2 q = dist S.triangle.v2 S.triangle.v3)
    (hBE : dist S.triangle.v2 E = dist S.triangle.v2 S.triangle.v3)
    (hDE : dist S.triangle.v3 E = dist S.triangle.v3 q)
    (hsmall : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v1 S.triangle.v2)
    (hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3)
    (hAElt : dist S.triangle.v1 E < dist S.triangle.v1 S.triangle.v2)
    (hEside :
      0 < signedArea2 E S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2)
    (hqE : q ≠ E) :
    0 ≤ (dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2)
        * (dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2) := by
  classical
  let q1 : ℝ² := S.triangle.v1
  let q2 : ℝ² := S.triangle.v2
  let q3 : ℝ² := S.triangle.v3
  have hq1ne : q1 ≠ q2 := by simpa [q1, q2] using S.triangle.v12_ne
  rcases b3n9m051_exists_base_transportData q1 q2 hq1ne with
    ⟨Tbase, tauBase, hv1Base, hv2Base⟩
  have horientBase_ne : tauBase.orientation ≠ 0 := by
    intro h0
    have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tauBase.orientation_sq
    norm_num at this
  have hq3_base_nonzero : (Tbase q3) 1 ≠ 0 := by
    have hq3_sa_ne : signedArea2 q3 q1 q2 ≠ 0 := by
      have hv1O : ‖q1 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q1] using S.Packet.moser_on_boundary_1
      have hv2O : ‖q2 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q2] using S.Packet.moser_on_boundary_2
      have hv3O : ‖q3 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q3] using S.Packet.moser_on_boundary_3
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        hv3O hv1O hv2O
        S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
    have himg_ne : signedArea2 (Tbase q3) (Tbase q1) (Tbase q2) ≠ 0 := by
      rw [tauBase.halfplane_sign q3 q1 q2]
      exact mul_ne_zero
        (mul_ne_zero horientBase_ne (pow_ne_zero 2 (ne_of_gt tauBase.scale_pos)))
        hq3_sa_ne
    intro h0
    apply himg_ne
    rw [hv1Base, hv2Base, b3n9m051_signedArea2_baseChord_vec2]
    linarith
  have build_from :
      ∀ {T0 : ℝ² → ℝ²},
        (tau0 : Problem97.CGN.SimilarityTransportData T0) →
        T0 q1 = Problem97.CGN.vec2 (-1) 0 →
        T0 q2 = Problem97.CGN.vec2 1 0 →
        0 < (T0 q3) 1 →
        0 ≤ (dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2)
            * (dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2) := by
    intro T0 tau0 hv1 hv2 hq3y_pos
    let T : ℝ² → ℝ² := fun x => b3n9m051_halfShift (T0 x)
    let tau : Problem97.CGN.SimilarityTransportData T :=
      b3n9m051_similarityTransportComp tau0 b3n9m051_halfShiftSimilarityTransportData
    have hv1T : T q1 = Problem97.CGN.vec2 0 0 := by
      dsimp [T]; rw [hv1]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2T : T q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [T]; rw [hv2]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3y_T : 0 < (T q3) 1 := by
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (0 : ℝ) < (T0 q3) 1 / 2 := by linarith
      simpa using this
    have hv2c0 : (T q2) 0 = 1 := by rw [hv2T]; simp [Problem97.CGN.vec2]
    have hv2c1 : (T q2) 1 = 0 := by rw [hv2T]; simp [Problem97.CGN.vec2]
    have hv1c0 : (T q1) 0 = 0 := by rw [hv1T]; simp [Problem97.CGN.vec2]
    have hv1c1 : (T q1) 1 = 0 := by rw [hv1T]; simp [Problem97.CGN.vec2]
    have hxAq : q ∈ A := S.CP.C3_subset (by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3))
    have hqC3 : q ∈ S.CP.C3 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3)
    have hq_ne_v1 : q ≠ q1 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqI3).2).1
    have hq_ne_v2 : q ≠ q2 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp hqI3).1
    have hxAqs : qs ∈ A := S.CP.C3_subset (by
      unfold Problem97.FiniteEndpointShell.I3 at hqsI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqsI3))
    have hqsC3 : qs ∈ S.CP.C3 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqsI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqsI3)
    have hqs_ne_v1 : qs ≠ q1 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqsI3
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqsI3).2).1
    have hqs_ne_v2 : qs ≠ q2 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqsI3
      exact (Finset.mem_erase.mp hqsI3).1
    have hq3_base_ne : signedArea2 q3 q1 q2 ≠ 0 := by
      have hv1O : dist q3 S.Packet.center = S.Packet.radius := by
        simpa [q3, dist_eq_norm] using S.Packet.moser_on_boundary_3
      have hv2O : dist q1 S.Packet.center = S.Packet.radius := by
        simpa [q1, dist_eq_norm] using S.Packet.moser_on_boundary_1
      have hv3O : dist q2 S.Packet.center = S.Packet.radius := by
        simpa [q2, dist_eq_norm] using S.Packet.moser_on_boundary_2
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        hv1O hv2O hv3O
        S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
    have hq3_img_pos : 0 < signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2]; linarith
    have hbelow : ∀ {x : ℝ²}, x ∈ A → x ∈ S.CP.C3 → x ≠ q1 → x ≠ q2 →
        (T x) 1 < 0 := by
      intro x hxA hxC3 hx_ne_v1 hx_ne_v2
      have hx_arc : signedArea2 x q1 q2 * signedArea2 q3 q1 q2 ≤ 0 :=
        (S.CP.arc_membership x hxA).2.2.1 hxC3
      have hx_base_ne : signedArea2 x q1 q2 ≠ 0 := by
        intro hz
        have hcol : Collinear ℝ ({x, q1, q2} : Set ℝ²) :=
          (Problem97.signedArea2_eq_zero_iff_collinear x q1 q2).1 hz
        exact False.elim <|
          (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) hxA S.triangle.v1_mem S.triangle.v2_mem
            hx_ne_v1 hx_ne_v2 S.triangle.v12_ne hcol
      have himg_nonpos :
          signedArea2 (T0 x) (T0 q1) (T0 q2) * signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 := by
        rw [tau0.halfplane_sign x q1 q2, tau0.halfplane_sign q3 q1 q2]
        have hrew :
            (tau0.orientation * (tau0.scale ^ 2) * signedArea2 x q1 q2) *
                (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q3 q1 q2) =
              (tau0.orientation ^ 2) * (tau0.scale ^ 2 * tau0.scale ^ 2) *
                (signedArea2 x q1 q2 * signedArea2 q3 q1 q2) := by ring
        rw [hrew, tau0.orientation_sq]
        have hscale_nonneg : 0 ≤ tau0.scale ^ 2 * tau0.scale ^ 2 := by positivity
        simpa using mul_nonpos_of_nonneg_of_nonpos hscale_nonneg hx_arc
      have hx_img_lt : signedArea2 (T0 x) (T0 q1) (T0 q2) < 0 := by
        have hx_img_le : signedArea2 (T0 x) (T0 q1) (T0 q2) ≤ 0 := by
          by_contra hx_pos
          have : 0 < signedArea2 (T0 x) (T0 q1) (T0 q2) *
              signedArea2 (T0 q3) (T0 q1) (T0 q2) := mul_pos (by linarith) hq3_img_pos
          linarith
        have hx_img_ne : signedArea2 (T0 x) (T0 q1) (T0 q2) ≠ 0 := by
          rw [tau0.halfplane_sign x q1 q2]
          have horient_ne : tau0.orientation ≠ 0 := by
            intro h0
            have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tau0.orientation_sq
            norm_num at this
          exact mul_ne_zero
            (mul_ne_zero horient_ne (pow_ne_zero 2 (ne_of_gt tau0.scale_pos))) hx_base_ne
        exact lt_of_le_of_ne hx_img_le hx_img_ne
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2] at hx_img_lt
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (T0 x) 1 / 2 < 0 := by linarith
      simpa using this
    have hqy_T : (T q) 1 < 0 := hbelow hxAq hqC3 hq_ne_v1 hq_ne_v2
    have hqsy_T : (T qs) 1 < 0 := hbelow hxAqs hqsC3 hqs_ne_v1 hqs_ne_v2
    have hE_base_ne : signedArea2 E q1 q2 ≠ 0 := by
      intro hz; rw [hz, zero_mul] at hEside; exact lt_irrefl _ hEside
    have hEy_T : 0 < (T E) 1 := by
      have hE_img_prod :
          0 < signedArea2 (T0 E) (T0 q1) (T0 q2) * signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
        rw [tau0.halfplane_sign E q1 q2, tau0.halfplane_sign q3 q1 q2]
        have hrew :
            (tau0.orientation * (tau0.scale ^ 2) * signedArea2 E q1 q2) *
                (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q3 q1 q2) =
              (tau0.orientation ^ 2) * (tau0.scale ^ 2 * tau0.scale ^ 2) *
                (signedArea2 E q1 q2 * signedArea2 q3 q1 q2) := by ring
        rw [hrew, tau0.orientation_sq]
        have hscale_pos : 0 < tau0.scale ^ 2 * tau0.scale ^ 2 := by
          have := tau0.scale_pos; positivity
        have hprod : 0 < signedArea2 E q1 q2 * signedArea2 q3 q1 q2 := by
          simpa [q1, q2, q3] using hEside
        have : 0 < tau0.scale ^ 2 * tau0.scale ^ 2 *
            (signedArea2 E q1 q2 * signedArea2 q3 q1 q2) := mul_pos hscale_pos hprod
        linarith [this]
      have hE_img_pos : 0 < signedArea2 (T0 E) (T0 q1) (T0 q2) := by
        by_contra hle
        push_neg at hle
        have : signedArea2 (T0 E) (T0 q1) (T0 q2) *
            signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hq3_img_pos)
        linarith
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2] at hE_img_pos
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (0 : ℝ) < (T0 E) 1 / 2 := by linarith
      simpa using this
    have hv3_ne_v2 : q3 ≠ q2 := by simpa [q2, q3] using S.triangle.v23_ne.symm
    set r : ℝ := dist (T q2) (T q3) with hr_def
    have hd_BD : 0 < dist q2 q3 := by rw [dist_pos]; exact fun h => hv3_ne_v2 h.symm
    have hr_pos : 0 < r := by
      rw [hr_def, tau.dist_image]; exact mul_pos tau.scale_pos hd_BD
    have hBD_T : dist (T q2) (T q3) = r := hr_def.symm
    have hBq_T : dist (T q2) (T q) = r := by
      rw [hr_def, tau.dist_image, tau.dist_image]
      have : dist q2 q = dist q2 q3 := by
        have := hBq; simp only [q2, q3] at this ⊢; rw [this]
      rw [this]
    have hBE_T : dist (T q2) (T E) = r := by
      rw [hr_def, tau.dist_image, tau.dist_image]
      have : dist q2 E = dist q2 q3 := by
        have := hBE; simp only [q2, q3] at this ⊢; rw [this]
      rw [this]
    have hDE_T : dist (T q3) (T E) = dist (T q3) (T q) := by
      rw [tau.dist_image, tau.dist_image]
      have : dist q3 E = dist q3 q := by
        have := hDE; simp only [q3] at this ⊢; rw [this]
      rw [this]
    have hDqs_T : dist (T q3) (T qs) = dist (T q3) (T q) := by
      rw [tau.dist_image, tau.dist_image]
      have : dist q3 qs = dist q3 q := by
        have := hDqs; simp only [q3] at this ⊢; rw [this]
      rw [this]
    set cδ : ℝ := ((T q3) 0 - 1) / r with hcδ_def
    set sδ : ℝ := (T q3) 1 / r with hsδ_def
    set cε : ℝ := ((T E) 0 - 1) / r with hcε_def
    set sε : ℝ := (T E) 1 / r with hsε_def
    set cη : ℝ := ((T q) 0 - 1) / r with hcη_def
    set sη : ℝ := (T q) 1 / r with hsη_def
    have hrne : r ≠ 0 := ne_of_gt hr_pos
    have hδpyth : cδ ^ 2 + sδ ^ 2 = 1 :=
      b3n9m051_circle_pyth (T q3) (T q2) r hrne hv2c0 hv2c1 hBD_T
    have hεpyth : cε ^ 2 + sε ^ 2 = 1 :=
      b3n9m051_circle_pyth (T E) (T q2) r hrne hv2c0 hv2c1 hBE_T
    have hηpyth : cη ^ 2 + sη ^ 2 = 1 :=
      b3n9m051_circle_pyth (T q) (T q2) r hrne hv2c0 hv2c1 hBq_T
    have hsδ_pos : 0 < sδ := by rw [hsδ_def]; positivity
    have hsε_pos : 0 < sε := by rw [hsε_def]; exact div_pos hEy_T hr_pos
    have hsη_neg : sη < 0 := by rw [hsη_def]; exact div_neg_of_neg_of_pos hqy_T hr_pos
    have hTD0 : (T q3) 0 = 1 + r * cδ := by rw [hcδ_def]; field_simp; ring
    have hTD1 : (T q3) 1 = r * sδ := by rw [hsδ_def]; field_simp
    have hTE0 : (T E) 0 = 1 + r * cε := by rw [hcε_def]; field_simp; ring
    have hTE1 : (T E) 1 = r * sε := by rw [hsε_def]; field_simp
    have hTq0 : (T q) 0 = 1 + r * cη := by rw [hcη_def]; field_simp; ring
    have hTq1 : (T q) 1 = r * sη := by rw [hsη_def]; field_simp
    have hradical : cη * cδ + sη * sδ = cε * cδ + sε * sδ := by
      have hsqeq : dist (T q3) (T E) ^ 2 = dist (T q3) (T q) ^ 2 := by rw [hDE_T]
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq] at hsqeq
      rw [hTD0, hTD1, hTE0, hTE1, hTq0, hTq1] at hsqeq
      have hkey : (cε * cδ + sε * sδ) * r ^ 2 = (cη * cδ + sη * sδ) * r ^ 2 := by
        nlinarith only [hsqeq, hεpyth, hηpyth, hδpyth]
      have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
      exact (mul_right_cancel₀ (ne_of_gt hr2pos) hkey).symm
    have hne : ¬ (cη = cε ∧ sη = sε) := by
      rintro ⟨hc, hs⟩
      apply hqE
      have h0 : (T q) 0 = (T E) 0 := by rw [hTq0, hTE0, hc]
      have h1 : (T q) 1 = (T E) 1 := by rw [hTq1, hTE1, hs]
      have hTqE : T q = T E := by ext i; fin_cases i
                                  · exact h0
                                  · exact h1
      have hd0 : dist (T q) (T E) = 0 := by rw [hTqE]; simp
      rw [tau.dist_image] at hd0
      have hdqE : dist q E = 0 := by
        rcases mul_eq_zero.mp hd0 with h | h
        · exact absurd h (ne_of_gt tau.scale_pos)
        · exact h
      exact dist_eq_zero.mp hdqE
    obtain ⟨ε, δ, hcosε, hsinε, _hε0, _hεπ, hcosδ, hsinδ, _hδ0, _hδπ, hcη_eq, hsη_eq⟩ :=
      b3n9m051_qEqE_reflection_coords r cε sε cδ sδ cη sη hsε_pos hεpyth hsδ_pos hδpyth hηpyth
        hsη_neg hradical hne
    have hsd : 0 < Real.sin δ := by rw [hsinδ]; exact hsδ_pos
    have hse : 0 < Real.sin ε := by rw [hsinε]; exact hsε_pos
    have hTD0' : (T q3) 0 = 1 + r * Real.cos δ := by rw [hTD0, ← hcosδ]
    have hTD1' : (T q3) 1 = r * Real.sin δ := by rw [hTD1, ← hsinδ]
    have hAB1 : dist (T q1) (T q2) = 1 := by
      rw [hv1T, hv2T, dist_eq_norm]
      have hvec :
          Problem97.CGN.vec2 0 0 - Problem97.CGN.vec2 1 0 = Problem97.CGN.vec2 (-1) 0 := by
        ext i <;> fin_cases i <;>
          simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
      rw [hvec, EuclideanSpace.norm_eq]
      norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hcd : -(r / 2) < Real.cos δ := by
      rw [hcosδ, hcδ_def]
      have hAD : 1 < dist (T q1) (T q3) := by
        rw [tau.dist_image]
        have hsc : dist (T q1) (T q2) = tau.scale * dist q1 q2 := tau.dist_image q1 q2
        rw [hAB1] at hsc
        have hlong' : dist q1 q2 < dist q1 q3 := by simpa [q1, q2, q3] using hlong
        nlinarith only [hsc, hlong, hlong', tau.scale_pos, dist_nonneg (x := q1) (y := q2)]
      have hADsq : 1 < (T q3) 0 ^ 2 + (T q3) 1 ^ 2 :=
        b3n9m051_normsq_gt_of_origin_dist_gt (T q3) (T q1) hv1c0 hv1c1 hAD
      exact b3n9m051_sign_pin_lower_bound r _ _ hr_pos (by rwa [← hcδ_def, ← hsδ_def]) hADsq
    have hce : Real.cos ε < -(r / 2) := by
      rw [hcosε, hcε_def]
      have hAE : dist (T q1) (T E) < 1 := by
        rw [tau.dist_image]
        have hsc : dist (T q1) (T q2) = tau.scale * dist q1 q2 := tau.dist_image q1 q2
        rw [hAB1] at hsc
        have hAElt' : dist q1 E < dist q1 q2 := by simpa [q1, q2] using hAElt
        nlinarith only [hsc, hAElt, hAElt', tau.scale_pos, dist_nonneg (x := q1) (y := q2)]
      have hAEsq : (T E) 0 ^ 2 + (T E) 1 ^ 2 < 1 :=
        b3n9m051_normsq_lt_of_origin_dist_lt (T E) (T q1) hv1c0 hv1c1 hAE
      exact b3n9m051_sign_pin_upper_bound r _ _ hr_pos (by rwa [← hcε_def, ← hsε_def]) hAEsq
    have hc2de : Real.cos (2 * δ - ε) < -(r / 2) := by
      rw [← hcη_eq, hcη_def]
      have hAq : dist (T q1) (T q) < 1 := by
        rw [tau.dist_image]
        have hsc : dist (T q1) (T q2) = tau.scale * dist q1 q2 := tau.dist_image q1 q2
        rw [hAB1] at hsc
        have hAqlt' : dist q1 q < dist q1 q2 := by
          simpa [q1, q2] using S.b3n9m051_v1_lt_v1v2_of_mem_I3 hqI3
        nlinarith only [hAqlt', hsmall, hsc, hd_BD, tau.scale_pos, dist_nonneg (x := q1) (y := q2)]
      have hAqsq : (T q) 0 ^ 2 + (T q) 1 ^ 2 < 1 :=
        b3n9m051_normsq_lt_of_origin_dist_lt (T q) (T q1) hv1c0 hv1c1 hAq
      exact b3n9m051_sign_pin_upper_bound r _ _ hr_pos (by rwa [← hcη_def, ← hsη_def]) hAqsq
    have hs2de : Real.sin (2 * δ - ε) < 0 := by rw [← hsη_eq]; exact hsη_neg
    have hDq_T_eq : dist (T q3) (T q) = r * Real.sqrt (2 - 2 * Real.cos (δ - ε)) := by
      have hDEdist : dist (T q3) (T E) ^ 2 = r ^ 2 * (2 - 2 * Real.cos (δ - ε)) := by
        rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, hTD0', hTD1', hTE0, hTE1, ← hcosε, ← hsinε,
            b3n9m051_chord_sq_formula r hr_pos δ ε]
        field_simp
      rw [hDE_T] at hDEdist
      exact b3n9m051_dist_eq_r_sqrt_of_sq _ r hr_pos δ ε dist_nonneg hDEdist
    set Sr : ℝ := Real.sqrt (2 - 2 * Real.cos (δ - ε)) with hSr_def
    have hS2eq : Sr ^ 2 = 2 - 2 * Real.cos (δ - ε) := by
      rw [hSr_def, Real.sq_sqrt]; nlinarith only [Real.cos_le_one (δ - ε)]
    have hq_ne_v3 : q ≠ q3 := by
      intro h; exact S.CP.v3_notin_C3 (by simpa [q3, h] using hqC3)
    have hSr_pos : 0 < Sr := by
      have hDq_pos : 0 < dist (T q3) (T q) := by
        rw [tau.dist_image]; apply mul_pos tau.scale_pos
        rw [dist_pos]; exact fun h => hq_ne_v3 h.symm
      show 0 < Real.sqrt (2 - 2 * Real.cos (δ - ε))
      have hh : Real.sqrt (2 - 2 * Real.cos (δ - ε)) = dist (T q3) (T q) / r := by
        rw [hDq_T_eq, mul_div_cancel_left₀ _ (ne_of_gt hr_pos)]
      rw [hh]; exact div_pos hDq_pos hr_pos
    have hDqsdist :
        ((T qs) 0 - (1 + r * Real.cos δ)) ^ 2 + ((T qs) 1 - r * Real.sin δ) ^ 2
          = (r * Sr) ^ 2 := by
      have h_coord : dist (T q3) (T qs) ^ 2 =
          ((T qs) 0 - (1 + r * Real.cos δ)) ^ 2 + ((T qs) 1 - r * Real.sin δ) ^ 2 := by
        rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, hTD0', hTD1']; ring
      rw [← h_coord, hDqs_T, hDq_T_eq]
    obtain ⟨t, hqsx, hqsy⟩ :=
      b3n9m051_qEqE_param_t r Sr (Real.cos δ) (Real.sin δ) ((T qs) 0) ((T qs) 1) hr_pos hSr_pos
        hDqsdist
    have hlower : r * Real.sin δ + r * Sr * Real.sin t < 0 := by
      rw [← hqsy]; exact hqsy_T
    have hr_lt_one : r < 1 := by
      have hBD : dist (T q2) (T q3) < dist (T q1) (T q2) := by
        rw [tau.dist_image, tau.dist_image]
        have hsc : 0 < tau.scale := tau.scale_pos
        have hlt : dist q2 q3 < dist q1 q2 := by simpa [q1, q2, q3] using hsmall
        nlinarith only [hsmall, hsc, hlt, dist_nonneg (x := q1) (y := q2)]
      rw [hBD_T, hAB1] at hBD; exact hBD
    have hB := qEqE_lowerArc_sameSign r δ ε t Sr hr_pos hr_lt_one
      hSr_pos hS2eq hsd hcd hse hce hs2de hc2de hlower
    rw [← b3n9m051_qEqE_f1_sinusoid r δ ε t Sr hS2eq, ← b3n9m051_qEqE_f2_sinusoid r δ ε t Sr] at hB
    have hqsx' : (T qs) 0 = (1 + r * Real.cos δ) + r * Sr * Real.cos t := by
      rw [hqsx]
    have hqsy' : (T qs) 1 = r * Real.sin δ + r * Sr * Real.sin t := hqsy
    have hTq0' : (T q) 0 = 1 + r * Real.cos (2 * δ - ε) := by rw [hTq0, hcη_eq]
    have hTq1' : (T q) 1 = r * Real.sin (2 * δ - ε) := by rw [hTq1, hsη_eq]
    have hGparam :
        (((1 + r * Real.cos δ) + r * Sr * Real.cos t) - (1 + r * Real.cos δ)) ^ 2
            + ((r * Real.sin δ + r * Sr * Real.sin t) - r * Real.sin δ) ^ 2
          = ((1 + r * Real.cos (2 * δ - ε)) - (1 + r * Real.cos δ)) ^ 2
            + (r * Real.sin (2 * δ - ε) - r * Real.sin δ) ^ 2 := by
      have hsq : dist (T q3) (T qs) ^ 2 = dist (T q3) (T q) ^ 2 := by rw [hDqs_T]
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq,
        hTD0', hTD1', hqsx', hqsy', hTq0', hTq1'] at hsq
      linarith [hsq]
    have hbridge2 :
        (((1 + r * Real.cos δ) + r * Sr * Real.cos t) - (1 + r * Real.cos (2 * δ - ε)))
              * ((1 + r * Real.cos δ) - 1)
            + (((r * Real.sin δ) + r * Sr * Real.sin t) - r * Real.sin (2 * δ - ε))
              * ((r * Real.sin δ) - 0)
          = (dist (T q2) (T qs) ^ 2 - dist (T q2) (T q) ^ 2) / 2 := by
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq,
        hv2c0, hv2c1, hqsx', hqsy', hTq0', hTq1']
      linear_combination (-(1 : ℝ) / 2) * hGparam
    have hbridge1 :
        (((1 + r * Real.cos δ) + r * Sr * Real.cos t) - (1 + r * Real.cos (2 * δ - ε)))
              * (1 + r * Real.cos δ)
            + (((r * Real.sin δ) + r * Sr * Real.sin t) - r * Real.sin (2 * δ - ε))
              * (r * Real.sin δ)
          = (dist (T q1) (T qs) ^ 2 - dist (T q1) (T q) ^ 2) / 2 := by
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq,
        hv1c0, hv1c1, hqsx', hqsy', hTq0', hTq1']
      linear_combination (-(1 : ℝ) / 2) * hGparam
    rw [hbridge2, hbridge1] at hB
    have hsc_pos : 0 < tau.scale := tau.scale_pos
    have hTB2qs : dist (T q2) (T qs) ^ 2 = tau.scale ^ 2 * dist q2 qs ^ 2 := by
      rw [tau.dist_image]; ring
    have hTB2q : dist (T q2) (T q) ^ 2 = tau.scale ^ 2 * dist q2 q ^ 2 := by
      rw [tau.dist_image]; ring
    have hTA2qs : dist (T q1) (T qs) ^ 2 = tau.scale ^ 2 * dist q1 qs ^ 2 := by
      rw [tau.dist_image]; ring
    have hTA2q : dist (T q1) (T q) ^ 2 = tau.scale ^ 2 * dist q1 q ^ 2 := by
      rw [tau.dist_image]; ring
    rw [hTB2qs, hTB2q, hTA2qs, hTA2q] at hB
    have hsc4 : 0 < tau.scale ^ 2 * tau.scale ^ 2 / 4 := by positivity
    have hfac :
        (tau.scale ^ 2 * dist q2 qs ^ 2 - tau.scale ^ 2 * dist q2 q ^ 2) / 2
            * ((tau.scale ^ 2 * dist q1 qs ^ 2 - tau.scale ^ 2 * dist q1 q ^ 2) / 2)
          = (dist q2 qs ^ 2 - dist q2 q ^ 2) * (dist q1 qs ^ 2 - dist q1 q ^ 2)
            * (tau.scale ^ 2 * tau.scale ^ 2 / 4) := by
      ring
    rw [hfac] at hB
    have hgoal :
        0 ≤ (dist q2 qs ^ 2 - dist q2 q ^ 2) * (dist q1 qs ^ 2 - dist q1 q ^ 2) :=
      nonneg_of_mul_nonneg_left hB hsc4
    simpa [q1, q2] using hgoal
  by_cases hq3pos : 0 < (Tbase q3) 1
  · exact build_from tauBase hv1Base hv2Base hq3pos
  · let Tflip : ℝ² → ℝ² := fun x => b3n9m051_flipY (Tbase x)
    let tauFlip : Problem97.CGN.SimilarityTransportData Tflip :=
      b3n9m051_similarityTransportComp tauBase b3n9m051_flipYSimilarityTransportData
    have hv1Flip : Tflip q1 = Problem97.CGN.vec2 (-1) 0 := by
      dsimp [Tflip]; rw [hv1Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2Flip : Tflip q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [Tflip]; rw [hv2Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3Flip : 0 < (Tflip q3) 1 := by
      dsimp [Tflip]
      simp only [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have hq3neg : (Tbase q3) 1 < 0 := by
        have hle : (Tbase q3) 1 ≤ 0 := le_of_not_gt hq3pos
        exact lt_of_le_of_ne hle hq3_base_nonzero
      simpa using hq3neg
    exact build_from tauFlip hv1Flip hv2Flip hq3Flip
set_option maxHeartbeats 8000000 in
theorem qEqE_lowerArc_sameSign_of_shell_flipped
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q qs E : ℝ²}
    (hqI3 : q ∈ S.I3) (hqsI3 : qs ∈ S.I3)
    (hDqs : dist S.triangle.v3 qs = dist S.triangle.v3 q)
    (hBq : dist S.triangle.v2 q = dist S.triangle.v2 S.triangle.v3)
    (hBE : dist S.triangle.v2 E = dist S.triangle.v2 S.triangle.v3)
    (hDE : dist S.triangle.v3 E = dist S.triangle.v3 q)
    (hsmall : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v1 S.triangle.v2)
    (hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3)
    (hAEgt : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 E)
    (hEC2 : E ∈ S.CP.C2)
    (hEside :
      0 < signedArea2 E S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2)
    (hqE : q ≠ E) :
    0 ≤ (dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2)
        * (dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2) := by
  classical
  let q1 : ℝ² := S.triangle.v1
  let q2 : ℝ² := S.triangle.v2
  let q3 : ℝ² := S.triangle.v3
  have hq1ne : q1 ≠ q2 := by simpa [q1, q2] using S.triangle.v12_ne
  rcases b3n9m051_exists_base_transportData q1 q2 hq1ne with
    ⟨Tbase, tauBase, hv1Base, hv2Base⟩
  have horientBase_ne : tauBase.orientation ≠ 0 := by
    intro h0
    have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tauBase.orientation_sq
    norm_num at this
  have hq3_base_nonzero : (Tbase q3) 1 ≠ 0 := by
    have hq3_sa_ne : signedArea2 q3 q1 q2 ≠ 0 := by
      have hv1O : ‖q1 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q1] using S.Packet.moser_on_boundary_1
      have hv2O : ‖q2 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q2] using S.Packet.moser_on_boundary_2
      have hv3O : ‖q3 - S.Packet.center‖ = S.Packet.radius := by
        simpa [q3] using S.Packet.moser_on_boundary_3
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        hv3O hv1O hv2O
        S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
    have himg_ne : signedArea2 (Tbase q3) (Tbase q1) (Tbase q2) ≠ 0 := by
      rw [tauBase.halfplane_sign q3 q1 q2]
      exact mul_ne_zero
        (mul_ne_zero horientBase_ne (pow_ne_zero 2 (ne_of_gt tauBase.scale_pos)))
        hq3_sa_ne
    intro h0
    apply himg_ne
    rw [hv1Base, hv2Base, b3n9m051_signedArea2_baseChord_vec2]
    linarith
  have build_from :
      ∀ {T0 : ℝ² → ℝ²},
        (tau0 : Problem97.CGN.SimilarityTransportData T0) →
        T0 q1 = Problem97.CGN.vec2 (-1) 0 →
        T0 q2 = Problem97.CGN.vec2 1 0 →
        0 < (T0 q3) 1 →
        0 ≤ (dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2)
            * (dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2) := by
    intro T0 tau0 hv1 hv2 hq3y_pos
    let T : ℝ² → ℝ² := fun x => b3n9m051_halfShift (T0 x)
    let tau : Problem97.CGN.SimilarityTransportData T :=
      b3n9m051_similarityTransportComp tau0 b3n9m051_halfShiftSimilarityTransportData
    have hv1T : T q1 = Problem97.CGN.vec2 0 0 := by
      dsimp [T]; rw [hv1]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2T : T q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [T]; rw [hv2]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3y_T : 0 < (T q3) 1 := by
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (0 : ℝ) < (T0 q3) 1 / 2 := by linarith
      simpa using this
    have hv2c0 : (T q2) 0 = 1 := by rw [hv2T]; simp [Problem97.CGN.vec2]
    have hv2c1 : (T q2) 1 = 0 := by rw [hv2T]; simp [Problem97.CGN.vec2]
    have hv1c0 : (T q1) 0 = 0 := by rw [hv1T]; simp [Problem97.CGN.vec2]
    have hv1c1 : (T q1) 1 = 0 := by rw [hv1T]; simp [Problem97.CGN.vec2]
    have hxAq : q ∈ A := S.CP.C3_subset (by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3))
    have hqC3 : q ∈ S.CP.C3 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI3)
    have hq_ne_v1 : q ≠ q1 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqI3).2).1
    have hq_ne_v2 : q ≠ q2 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqI3
      exact (Finset.mem_erase.mp hqI3).1
    have hxAqs : qs ∈ A := S.CP.C3_subset (by
      unfold Problem97.FiniteEndpointShell.I3 at hqsI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqsI3))
    have hqsC3 : qs ∈ S.CP.C3 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqsI3
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqsI3)
    have hqs_ne_v1 : qs ≠ q1 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqsI3
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqsI3).2).1
    have hqs_ne_v2 : qs ≠ q2 := by
      unfold Problem97.FiniteEndpointShell.I3 at hqsI3
      exact (Finset.mem_erase.mp hqsI3).1
    have hq3_base_ne : signedArea2 q3 q1 q2 ≠ 0 := by
      have hv1O : dist q3 S.Packet.center = S.Packet.radius := by
        simpa [q3, dist_eq_norm] using S.Packet.moser_on_boundary_3
      have hv2O : dist q1 S.Packet.center = S.Packet.radius := by
        simpa [q1, dist_eq_norm] using S.Packet.moser_on_boundary_1
      have hv3O : dist q2 S.Packet.center = S.Packet.radius := by
        simpa [q2, dist_eq_norm] using S.Packet.moser_on_boundary_2
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        hv1O hv2O hv3O
        S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
    have hq3_img_pos : 0 < signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2]; linarith
    have hbelow : ∀ {x : ℝ²}, x ∈ A → x ∈ S.CP.C3 → x ≠ q1 → x ≠ q2 →
        (T x) 1 < 0 := by
      intro x hxA hxC3 hx_ne_v1 hx_ne_v2
      have hx_arc : signedArea2 x q1 q2 * signedArea2 q3 q1 q2 ≤ 0 :=
        (S.CP.arc_membership x hxA).2.2.1 hxC3
      have hx_base_ne : signedArea2 x q1 q2 ≠ 0 := by
        intro hz
        have hcol : Collinear ℝ ({x, q1, q2} : Set ℝ²) :=
          (Problem97.signedArea2_eq_zero_iff_collinear x q1 q2).1 hz
        exact False.elim <|
          (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) hxA S.triangle.v1_mem S.triangle.v2_mem
            hx_ne_v1 hx_ne_v2 S.triangle.v12_ne hcol
      have himg_nonpos :
          signedArea2 (T0 x) (T0 q1) (T0 q2) * signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 := by
        rw [tau0.halfplane_sign x q1 q2, tau0.halfplane_sign q3 q1 q2]
        have hrew :
            (tau0.orientation * (tau0.scale ^ 2) * signedArea2 x q1 q2) *
                (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q3 q1 q2) =
              (tau0.orientation ^ 2) * (tau0.scale ^ 2 * tau0.scale ^ 2) *
                (signedArea2 x q1 q2 * signedArea2 q3 q1 q2) := by ring
        rw [hrew, tau0.orientation_sq]
        have hscale_nonneg : 0 ≤ tau0.scale ^ 2 * tau0.scale ^ 2 := by positivity
        simpa using mul_nonpos_of_nonneg_of_nonpos hscale_nonneg hx_arc
      have hx_img_lt : signedArea2 (T0 x) (T0 q1) (T0 q2) < 0 := by
        have hx_img_le : signedArea2 (T0 x) (T0 q1) (T0 q2) ≤ 0 := by
          by_contra hx_pos
          have : 0 < signedArea2 (T0 x) (T0 q1) (T0 q2) *
              signedArea2 (T0 q3) (T0 q1) (T0 q2) := mul_pos (by linarith) hq3_img_pos
          linarith
        have hx_img_ne : signedArea2 (T0 x) (T0 q1) (T0 q2) ≠ 0 := by
          rw [tau0.halfplane_sign x q1 q2]
          have horient_ne : tau0.orientation ≠ 0 := by
            intro h0
            have : (0 : ℝ) ^ 2 = 1 := by simpa [h0] using tau0.orientation_sq
            norm_num at this
          exact mul_ne_zero
            (mul_ne_zero horient_ne (pow_ne_zero 2 (ne_of_gt tau0.scale_pos))) hx_base_ne
        exact lt_of_le_of_ne hx_img_le hx_img_ne
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2] at hx_img_lt
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (T0 x) 1 / 2 < 0 := by linarith
      simpa using this
    have hqy_T : (T q) 1 < 0 := hbelow hxAq hqC3 hq_ne_v1 hq_ne_v2
    have hqsy_T : (T qs) 1 < 0 := hbelow hxAqs hqsC3 hqs_ne_v1 hqs_ne_v2
    have hE_base_ne : signedArea2 E q1 q2 ≠ 0 := by
      intro hz; rw [hz, zero_mul] at hEside; exact lt_irrefl _ hEside
    have hEy_T : 0 < (T E) 1 := by
      have hE_img_prod :
          0 < signedArea2 (T0 E) (T0 q1) (T0 q2) * signedArea2 (T0 q3) (T0 q1) (T0 q2) := by
        rw [tau0.halfplane_sign E q1 q2, tau0.halfplane_sign q3 q1 q2]
        have hrew :
            (tau0.orientation * (tau0.scale ^ 2) * signedArea2 E q1 q2) *
                (tau0.orientation * (tau0.scale ^ 2) * signedArea2 q3 q1 q2) =
              (tau0.orientation ^ 2) * (tau0.scale ^ 2 * tau0.scale ^ 2) *
                (signedArea2 E q1 q2 * signedArea2 q3 q1 q2) := by ring
        rw [hrew, tau0.orientation_sq]
        have hscale_pos : 0 < tau0.scale ^ 2 * tau0.scale ^ 2 := by
          have := tau0.scale_pos; positivity
        have hprod : 0 < signedArea2 E q1 q2 * signedArea2 q3 q1 q2 := by
          simpa [q1, q2, q3] using hEside
        have : 0 < tau0.scale ^ 2 * tau0.scale ^ 2 *
            (signedArea2 E q1 q2 * signedArea2 q3 q1 q2) := mul_pos hscale_pos hprod
        linarith [this]
      have hE_img_pos : 0 < signedArea2 (T0 E) (T0 q1) (T0 q2) := by
        by_contra hle
        push_neg at hle
        have : signedArea2 (T0 E) (T0 q1) (T0 q2) *
            signedArea2 (T0 q3) (T0 q1) (T0 q2) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hq3_img_pos)
        linarith
      rw [hv1, hv2, b3n9m051_signedArea2_baseChord_vec2] at hE_img_pos
      dsimp [T]
      simp only [b3n9m051_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have : (0 : ℝ) < (T0 E) 1 / 2 := by linarith
      simpa using this
    have hv3_ne_v2 : q3 ≠ q2 := by simpa [q2, q3] using S.triangle.v23_ne.symm
    set r : ℝ := dist (T q2) (T q3) with hr_def
    have hd_BD : 0 < dist q2 q3 := by rw [dist_pos]; exact fun h => hv3_ne_v2 h.symm
    have hr_pos : 0 < r := by
      rw [hr_def, tau.dist_image]; exact mul_pos tau.scale_pos hd_BD
    have hBD_T : dist (T q2) (T q3) = r := hr_def.symm
    have hBq_T : dist (T q2) (T q) = r := by
      rw [hr_def, tau.dist_image, tau.dist_image]
      have : dist q2 q = dist q2 q3 := by
        have := hBq; simp only [q2, q3] at this ⊢; rw [this]
      rw [this]
    have hBE_T : dist (T q2) (T E) = r := by
      rw [hr_def, tau.dist_image, tau.dist_image]
      have : dist q2 E = dist q2 q3 := by
        have := hBE; simp only [q2, q3] at this ⊢; rw [this]
      rw [this]
    have hDE_T : dist (T q3) (T E) = dist (T q3) (T q) := by
      rw [tau.dist_image, tau.dist_image]
      have : dist q3 E = dist q3 q := by
        have := hDE; simp only [q3] at this ⊢; rw [this]
      rw [this]
    have hDqs_T : dist (T q3) (T qs) = dist (T q3) (T q) := by
      rw [tau.dist_image, tau.dist_image]
      have : dist q3 qs = dist q3 q := by
        have := hDqs; simp only [q3] at this ⊢; rw [this]
      rw [this]
    set cδ : ℝ := ((T q3) 0 - 1) / r with hcδ_def
    set sδ : ℝ := (T q3) 1 / r with hsδ_def
    set cε : ℝ := ((T E) 0 - 1) / r with hcε_def
    set sε : ℝ := (T E) 1 / r with hsε_def
    set cη : ℝ := ((T q) 0 - 1) / r with hcη_def
    set sη : ℝ := (T q) 1 / r with hsη_def
    have hrne : r ≠ 0 := ne_of_gt hr_pos
    have hδpyth : cδ ^ 2 + sδ ^ 2 = 1 :=
      b3n9m051_circle_pyth (T q3) (T q2) r hrne hv2c0 hv2c1 hBD_T
    have hεpyth : cε ^ 2 + sε ^ 2 = 1 :=
      b3n9m051_circle_pyth (T E) (T q2) r hrne hv2c0 hv2c1 hBE_T
    have hηpyth : cη ^ 2 + sη ^ 2 = 1 :=
      b3n9m051_circle_pyth (T q) (T q2) r hrne hv2c0 hv2c1 hBq_T
    have hsδ_pos : 0 < sδ := by rw [hsδ_def]; exact div_pos hq3y_T hr_pos
    have hsε_pos : 0 < sε := by rw [hsε_def]; exact div_pos hEy_T hr_pos
    have hsη_neg : sη < 0 := by rw [hsη_def]; exact div_neg_of_neg_of_pos hqy_T hr_pos
    have hTD0 : (T q3) 0 = 1 + r * cδ := by rw [hcδ_def]; field_simp; ring
    have hTD1 : (T q3) 1 = r * sδ := by rw [hsδ_def]; field_simp
    have hTE0 : (T E) 0 = 1 + r * cε := by rw [hcε_def]; field_simp; ring
    have hTE1 : (T E) 1 = r * sε := by rw [hsε_def]; field_simp
    have hTq0 : (T q) 0 = 1 + r * cη := by rw [hcη_def]; field_simp; ring
    have hTq1 : (T q) 1 = r * sη := by rw [hsη_def]; field_simp
    have hradical : cη * cδ + sη * sδ = cε * cδ + sε * sδ := by
      have hsqeq : dist (T q3) (T E) ^ 2 = dist (T q3) (T q) ^ 2 := by rw [hDE_T]
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq] at hsqeq
      rw [hTD0, hTD1, hTE0, hTE1, hTq0, hTq1] at hsqeq
      have hkey : (cε * cδ + sε * sδ) * r ^ 2 = (cη * cδ + sη * sδ) * r ^ 2 := by
        nlinarith only [hsqeq, hεpyth, hηpyth, hδpyth]
      have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
      exact (mul_right_cancel₀ (ne_of_gt hr2pos) hkey).symm
    have hne : ¬ (cη = cε ∧ sη = sε) := by
      rintro ⟨hc, hs⟩
      apply hqE
      have h0 : (T q) 0 = (T E) 0 := by rw [hTq0, hTE0, hc]
      have h1 : (T q) 1 = (T E) 1 := by rw [hTq1, hTE1, hs]
      have hTqE : T q = T E := by ext i; fin_cases i
                                  · exact h0
                                  · exact h1
      have hd0 : dist (T q) (T E) = 0 := by rw [hTqE]; simp
      rw [tau.dist_image] at hd0
      have hdqE : dist q E = 0 := by
        rcases mul_eq_zero.mp hd0 with h | h
        · exact absurd h (ne_of_gt tau.scale_pos)
        · exact h
      exact dist_eq_zero.mp hdqE
    obtain ⟨ε, δ, hcosε, hsinε, hε0, hεπ, hcosδ, hsinδ, hδ0, hδπ, hcη_eq, hsη_eq⟩ :=
      b3n9m051_qEqE_reflection_coords r cε sε cδ sδ cη sη hsε_pos hεpyth hsδ_pos hδpyth hηpyth
        hsη_neg hradical hne
    have hsd : 0 < Real.sin δ := by rw [hsinδ]; exact hsδ_pos
    have hse : 0 < Real.sin ε := by rw [hsinε]; exact hsε_pos
    have hTD0' : (T q3) 0 = 1 + r * Real.cos δ := by rw [hTD0, ← hcosδ]
    have hTD1' : (T q3) 1 = r * Real.sin δ := by rw [hTD1, ← hsinδ]
    have hTE0' : (T E) 0 = 1 + r * Real.cos ε := by rw [hTE0, ← hcosε]
    have hTE1' : (T E) 1 = r * Real.sin ε := by rw [hTE1, ← hsinε]
    have hEC2_arc :
        signedArea2 E q3 q1 * signedArea2 q2 q3 q1 ≤ 0 := by
      have hEA : E ∈ A := S.CP.C2_subset hEC2
      have h := ((S.CP.arc_membership E hEA).2.1).mp hEC2
      simpa [Problem97.OnArcOpposite, q1, q2, q3] using h
    have hEC2_img :
        signedArea2 (T E) (T q3) (T q1) *
            signedArea2 (T q2) (T q3) (T q1) ≤ 0 := by
      rw [tau.halfplane_sign E q3 q1, tau.halfplane_sign q2 q3 q1]
      have hrew :
          (tau.orientation * (tau.scale ^ 2) * signedArea2 E q3 q1) *
              (tau.orientation * (tau.scale ^ 2) * signedArea2 q2 q3 q1) =
            (tau.orientation ^ 2) * (tau.scale ^ 2 * tau.scale ^ 2) *
              (signedArea2 E q3 q1 * signedArea2 q2 q3 q1) := by ring
      rw [hrew, tau.orientation_sq]
      have hscale_nonneg : 0 ≤ tau.scale ^ 2 * tau.scale ^ 2 := by positivity
      simpa using mul_nonpos_of_nonneg_of_nonpos hscale_nonneg hEC2_arc
    set side : ℝ :=
      Real.sin δ - Real.sin ε
        - r * (Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ) with hside_def
    have hE_c2_area : signedArea2 (T E) (T q3) (T q1) = r * side := by
      rw [Problem97.signedArea2, hTE0', hTE1', hTD0', hTD1', hv1T, hside_def]
      simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
      ring
    have hq2_c2_area : signedArea2 (T q2) (T q3) (T q1) = r * Real.sin δ := by
      rw [Problem97.signedArea2, hv2T, hTD0', hTD1', hv1T]
      simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hside_scaled : r * side ≤ 0 := by
      have hprod : (r * side) * (r * Real.sin δ) ≤ 0 := by
        simpa [hE_c2_area, hq2_c2_area] using hEC2_img
      have hfactor_pos : 0 < r * Real.sin δ := mul_pos hr_pos hsd
      by_contra hpos
      push_neg at hpos
      have : 0 < (r * side) * (r * Real.sin δ) := mul_pos hpos hfactor_pos
      linarith
    have hside : Real.sin δ - Real.sin ε
        - r * (Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ) ≤ 0 := by
      have hside_le : side ≤ 0 := by
        by_contra hpos
        push_neg at hpos
        have : 0 < r * side := mul_pos hr_pos hpos
        linarith
      simpa [hside_def] using hside_le
    have hAB1 : dist (T q1) (T q2) = 1 := by
      rw [hv1T, hv2T, dist_eq_norm]
      have hvec :
          Problem97.CGN.vec2 0 0 - Problem97.CGN.vec2 1 0 = Problem97.CGN.vec2 (-1) 0 := by
        ext i <;> fin_cases i <;>
          simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
      rw [hvec, EuclideanSpace.norm_eq]
      norm_num [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hcd : -(r / 2) < Real.cos δ := by
      rw [hcosδ, hcδ_def]
      have hAD : 1 < dist (T q1) (T q3) := by
        rw [tau.dist_image]
        have hsc : dist (T q1) (T q2) = tau.scale * dist q1 q2 := tau.dist_image q1 q2
        rw [hAB1] at hsc
        have hlong' : dist q1 q2 < dist q1 q3 := by simpa [q1, q2, q3] using hlong
        nlinarith only [hsc, hlong, hlong', tau.scale_pos, dist_nonneg (x := q1) (y := q2)]
      have hADsq : 1 < (T q3) 0 ^ 2 + (T q3) 1 ^ 2 :=
        b3n9m051_normsq_gt_of_origin_dist_gt (T q3) (T q1) hv1c0 hv1c1 hAD
      exact b3n9m051_sign_pin_lower_bound r _ _ hr_pos (by rwa [← hcδ_def, ← hsδ_def]) hADsq
    have hs2de : Real.sin (2 * δ - ε) < 0 := by rw [← hsη_eq]; exact hsη_neg
    have hDq_T_eq : dist (T q3) (T q) = r * Real.sqrt (2 - 2 * Real.cos (δ - ε)) := by
      have hDEdist : dist (T q3) (T E) ^ 2 = r ^ 2 * (2 - 2 * Real.cos (δ - ε)) := by
        rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, hTD0', hTD1', hTE0, hTE1, ← hcosε, ← hsinε,
            b3n9m051_chord_sq_formula r hr_pos δ ε]
        field_simp
      rw [hDE_T] at hDEdist
      exact b3n9m051_dist_eq_r_sqrt_of_sq _ r hr_pos δ ε dist_nonneg hDEdist
    set Sr : ℝ := Real.sqrt (2 - 2 * Real.cos (δ - ε)) with hSr_def
    have hS2eq : Sr ^ 2 = 2 - 2 * Real.cos (δ - ε) := by
      rw [hSr_def, Real.sq_sqrt]; nlinarith only [Real.cos_le_one (δ - ε)]
    have hq_ne_v3 : q ≠ q3 := by
      intro h; exact S.CP.v3_notin_C3 (by simpa [q3, h] using hqC3)
    have hSr_pos : 0 < Sr := by
      have hDq_pos : 0 < dist (T q3) (T q) := by
        rw [tau.dist_image]; apply mul_pos tau.scale_pos
        rw [dist_pos]; exact fun h => hq_ne_v3 h.symm
      show 0 < Real.sqrt (2 - 2 * Real.cos (δ - ε))
      have hh : Real.sqrt (2 - 2 * Real.cos (δ - ε)) = dist (T q3) (T q) / r := by
        rw [hDq_T_eq, mul_div_cancel_left₀ _ (ne_of_gt hr_pos)]
      rw [hh]; exact div_pos hDq_pos hr_pos
    have hDqsdist :
        ((T qs) 0 - (1 + r * Real.cos δ)) ^ 2 + ((T qs) 1 - r * Real.sin δ) ^ 2
          = (r * Sr) ^ 2 := by
      have h_coord : dist (T q3) (T qs) ^ 2 =
          ((T qs) 0 - (1 + r * Real.cos δ)) ^ 2 + ((T qs) 1 - r * Real.sin δ) ^ 2 := by
        rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, hTD0', hTD1']; ring
      rw [← h_coord, hDqs_T, hDq_T_eq]
    obtain ⟨t, hqsx, hqsy⟩ :=
      b3n9m051_qEqE_param_t r Sr (Real.cos δ) (Real.sin δ) ((T qs) 0) ((T qs) 1) hr_pos hSr_pos
        hDqsdist
    have hlower : r * Real.sin δ + r * Sr * Real.sin t < 0 := by
      rw [← hqsy]; exact hqsy_T
    have hB := qEqE_lowerArc_sameSign_flipped_of_c2Side r δ ε t Sr hr_pos
      hSr_pos hS2eq hsd hcd hse hδ0 hδπ hε0 hεπ hs2de hside hlower
    rw [← b3n9m051_qEqE_f1_sinusoid r δ ε t Sr hS2eq, ← b3n9m051_qEqE_f2_sinusoid r δ ε t Sr] at hB
    have hqsx' : (T qs) 0 = (1 + r * Real.cos δ) + r * Sr * Real.cos t := by
      rw [hqsx]
    have hqsy' : (T qs) 1 = r * Real.sin δ + r * Sr * Real.sin t := hqsy
    have hTq0' : (T q) 0 = 1 + r * Real.cos (2 * δ - ε) := by rw [hTq0, hcη_eq]
    have hTq1' : (T q) 1 = r * Real.sin (2 * δ - ε) := by rw [hTq1, hsη_eq]
    have hGparam :
        (((1 + r * Real.cos δ) + r * Sr * Real.cos t) - (1 + r * Real.cos δ)) ^ 2
            + ((r * Real.sin δ + r * Sr * Real.sin t) - r * Real.sin δ) ^ 2
          = ((1 + r * Real.cos (2 * δ - ε)) - (1 + r * Real.cos δ)) ^ 2
            + (r * Real.sin (2 * δ - ε) - r * Real.sin δ) ^ 2 := by
      have hsq : dist (T q3) (T qs) ^ 2 = dist (T q3) (T q) ^ 2 := by rw [hDqs_T]
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq,
        hTD0', hTD1', hqsx', hqsy', hTq0', hTq1'] at hsq
      linarith [hsq]
    have hbridge2 :
        (((1 + r * Real.cos δ) + r * Sr * Real.cos t) - (1 + r * Real.cos (2 * δ - ε)))
              * ((1 + r * Real.cos δ) - 1)
            + (((r * Real.sin δ) + r * Sr * Real.sin t) - r * Real.sin (2 * δ - ε))
              * ((r * Real.sin δ) - 0)
          = (dist (T q2) (T qs) ^ 2 - dist (T q2) (T q) ^ 2) / 2 := by
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq,
        hv2c0, hv2c1, hqsx', hqsy', hTq0', hTq1']
      linear_combination (-(1 : ℝ) / 2) * hGparam
    have hbridge1 :
        (((1 + r * Real.cos δ) + r * Sr * Real.cos t) - (1 + r * Real.cos (2 * δ - ε)))
              * (1 + r * Real.cos δ)
            + (((r * Real.sin δ) + r * Sr * Real.sin t) - r * Real.sin (2 * δ - ε))
              * (r * Real.sin δ)
          = (dist (T q1) (T qs) ^ 2 - dist (T q1) (T q) ^ 2) / 2 := by
      rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq,
        hv1c0, hv1c1, hqsx', hqsy', hTq0', hTq1']
      linear_combination (-(1 : ℝ) / 2) * hGparam
    rw [hbridge2, hbridge1] at hB
    have hsc_pos : 0 < tau.scale := tau.scale_pos
    have hTB2qs : dist (T q2) (T qs) ^ 2 = tau.scale ^ 2 * dist q2 qs ^ 2 := by
      rw [tau.dist_image]; ring
    have hTB2q : dist (T q2) (T q) ^ 2 = tau.scale ^ 2 * dist q2 q ^ 2 := by
      rw [tau.dist_image]; ring
    have hTA2qs : dist (T q1) (T qs) ^ 2 = tau.scale ^ 2 * dist q1 qs ^ 2 := by
      rw [tau.dist_image]; ring
    have hTA2q : dist (T q1) (T q) ^ 2 = tau.scale ^ 2 * dist q1 q ^ 2 := by
      rw [tau.dist_image]; ring
    rw [hTB2qs, hTB2q, hTA2qs, hTA2q] at hB
    have hsc4 : 0 < tau.scale ^ 2 * tau.scale ^ 2 / 4 := by positivity
    have hfac :
        (tau.scale ^ 2 * dist q2 qs ^ 2 - tau.scale ^ 2 * dist q2 q ^ 2) / 2
            * ((tau.scale ^ 2 * dist q1 qs ^ 2 - tau.scale ^ 2 * dist q1 q ^ 2) / 2)
          = (dist q2 qs ^ 2 - dist q2 q ^ 2) * (dist q1 qs ^ 2 - dist q1 q ^ 2)
            * (tau.scale ^ 2 * tau.scale ^ 2 / 4) := by
      ring
    rw [hfac] at hB
    have hgoal :
        0 ≤ (dist q2 qs ^ 2 - dist q2 q ^ 2) * (dist q1 qs ^ 2 - dist q1 q ^ 2) :=
      nonneg_of_mul_nonneg_left hB hsc4
    simpa [q1, q2] using hgoal
  by_cases hq3pos : 0 < (Tbase q3) 1
  · exact build_from tauBase hv1Base hv2Base hq3pos
  · let Tflip : ℝ² → ℝ² := fun x => b3n9m051_flipY (Tbase x)
    let tauFlip : Problem97.CGN.SimilarityTransportData Tflip :=
      b3n9m051_similarityTransportComp tauBase b3n9m051_flipYSimilarityTransportData
    have hv1Flip : Tflip q1 = Problem97.CGN.vec2 (-1) 0 := by
      dsimp [Tflip]; rw [hv1Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2Flip : Tflip q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [Tflip]; rw [hv2Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3Flip : 0 < (Tflip q3) 1 := by
      dsimp [Tflip]
      simp only [b3n9m051_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      have hq3neg : (Tbase q3) 1 < 0 := by
        have hle : (Tbase q3) 1 ≤ 0 := le_of_not_gt hq3pos
        exact lt_of_le_of_ne hle hq3_base_nonzero
      simpa using hq3neg
    exact build_from tauFlip hv1Flip hv2Flip hq3Flip
theorem qEqE_lowerArc_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q qs E : ℝ²}
    (hqI3 : q ∈ S.I3) (hqsI3 : qs ∈ S.I3)
    (hDqs : dist S.triangle.v3 qs = dist S.triangle.v3 q)
    (hBq : dist S.triangle.v2 q = dist S.triangle.v2 S.triangle.v3)
    (hBE : dist S.triangle.v2 E = dist S.triangle.v2 S.triangle.v3)
    (hDE : dist S.triangle.v3 E = dist S.triangle.v3 q)
    (hsmall : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v1 S.triangle.v2)
    (hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3)
    (hAElt : dist S.triangle.v1 E < dist S.triangle.v1 S.triangle.v2)
    (hEside :
      0 < signedArea2 E S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2)
    (hqE : q ≠ E)
    (hcap_opp :
      (dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2)
        * (dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2) < 0) :
    False := by
  have hsign := S.qEqE_lowerArc_sameSign_of_shell hqI3 hqsI3 hDqs hBq hBE hDE
    hsmall hlong hAElt hEside hqE
  linarith [hsign, hcap_opp]
theorem qEqE_lowerArc_impossible_flipped
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {q qs E : ℝ²}
    (hqI3 : q ∈ S.I3) (hqsI3 : qs ∈ S.I3)
    (hDqs : dist S.triangle.v3 qs = dist S.triangle.v3 q)
    (hBq : dist S.triangle.v2 q = dist S.triangle.v2 S.triangle.v3)
    (hBE : dist S.triangle.v2 E = dist S.triangle.v2 S.triangle.v3)
    (hDE : dist S.triangle.v3 E = dist S.triangle.v3 q)
    (hsmall : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v1 S.triangle.v2)
    (hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3)
    (hAEgt : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 E)
    (hEC2 : E ∈ S.CP.C2)
    (hEside :
      0 < signedArea2 E S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2)
    (hqE : q ≠ E)
    (hcap_opp :
      (dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2)
        * (dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2) < 0) :
    False := by
  have hsign := S.qEqE_lowerArc_sameSign_of_shell_flipped hqI3 hqsI3 hDqs hBq hBE hDE
    hsmall hlong hAEgt hEC2 hEside hqE
  linarith [hsign, hcap_opp]

end FiniteEndpointShell
end Problem97
end Batch3N9

/-- The middle N4e slice exports its Form B branch conclusions. -/
theorem solution {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A)
    (Z : Batch3N9.Problem97.FiniteEndpointShell.ZeroDefectCapLayout S) :
    Nonempty
      (Batch3N9.Problem97.FiniteEndpointShell.N4dFormBBranchSupport S Z) := by
  exact ⟨{
    v1v3_longer_than_base_of_exact_packet := S.v1v3_longer_than_base_of_exact_packet Z
    selectorShape_v3_q_eq_a2_impossible_of_exact_packet := S.selectorShape_v3_q_eq_a2_impossible_of_exact_packet Z
    n4d_bB_2_q_eq_v1_impossible := S.n4d_bB_2_q_eq_v1_impossible Z
    n4d_bA_2_q_eq_v1_impossible := S.n4d_bA_2_q_eq_v1_impossible Z
    n4d_bA_2_q_eq_C_impossible := S.n4d_bA_2_q_eq_C_impossible Z
    qEqE_row_impossible_of_reflection := S.qEqE_row_impossible_of_reflection
    qEqE_lowerArc_impossible := S.qEqE_lowerArc_impossible
    qEqE_lowerArc_impossible_flipped := S.qEqE_lowerArc_impossible_flipped
  }⟩
