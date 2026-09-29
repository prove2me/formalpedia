-- Prove2me | solution 1 for Erdos9796FiniteNine.single_apex_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T07:45:36.488255+00:00
-- url     : https://prove2.me/submissions/d578752d-d17e-46cf-b111-ae3d7aec65a2

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Erdos9796FiniteNine_N8Interface
import Theorems.Thm_Erdos9796FiniteNine_circle_placement

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

-- Original module: Solutions.Batch3N9.TwoCircleCrossing
section Batch3N9Unit047
namespace Batch3N9
open scoped EuclideanGeometry
open EuclideanGeometry
namespace Problem97
theorem two_circle_common_point_eq_endpoint
    {s₁ s₂ : Sphere ℝ²} (hs : s₁ ≠ s₂) {p₁ p₂ q : ℝ²} (hp : p₁ ≠ p₂)
    (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂)
    (hqs₁ : q ∈ s₁) (hqs₂ : q ∈ s₂) : q = p₁ ∨ q = p₂ :=
  eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
    finrank_euclideanSpace_fin hs hp hp₁s₁ hp₂s₁ hqs₁ hp₁s₂ hp₂s₂ hqs₂
end Problem97
end Batch3N9
end Batch3N9Unit047

-- Original module: Solutions.Batch3N9.ArcBlockContiguity
section Batch3N9Unit048
namespace Batch3N9
open scoped EuclideanGeometry
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit048

-- Original module: Solutions.Batch3N9.U2.WitnessReflectionKernel
section Batch3N9Unit049
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open EuclideanGeometry
namespace Problem97
theorem inner_sub_centers_eq_zero
    {a b u y : ℝ²} (hua : dist u a = dist y a) (hub : dist u b = dist y b) :
    ⟪u - y, a - b⟫_ℝ = 0 := by
  have h := EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
    (c₁ := b) (c₂ := a) (p₁ := y) (p₂ := u) (by rw [hub]) (by rw [hua])
  simpa only [vsub_eq_sub, real_inner_comm] using h
theorem twoCircle_midpoint_collinear {q v2 u y : ℝ²} {rq rv : ℝ}
    (huq : dist u q = rq) (hyq : dist y q = rq)
    (huv : dist u v2 = rv) (hyv : dist y v2 = rv)
    (hne : u ≠ y) :
    signedArea2 (midpoint ℝ y u) q v2 = 0 := by
  have huqyq : dist u q = dist y q := huq.trans hyq.symm
  have huvyv : dist u v2 = dist y v2 := huv.trans hyv.symm
  have hum : dist u (midpoint ℝ y u) = dist y (midpoint ℝ y u) := by
    rw [dist_comm u, dist_comm y]; rw [dist_midpoint_left, dist_midpoint_right]
  have hperp1 : ⟪u - y, q - v2⟫_ℝ = 0 := inner_sub_centers_eq_zero huqyq huvyv
  have hperp2 : ⟪u - y, q - midpoint ℝ y u⟫_ℝ = 0 :=
    inner_sub_centers_eq_zero huqyq hum
  have h1 : (u 0 - y 0) * (q 0 - v2 0) + (u 1 - y 1) * (q 1 - v2 1) = 0 := by
    simp [EuclideanSpace.inner_eq_star_dotProduct] at hperp1; linarith
  have h2 : (u 0 - y 0) * (q 0 - (y 0 + u 0) / 2) +
            (u 1 - y 1) * (q 1 - (y 1 + u 1) / 2) = 0 := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, midpoint, AffineMap.lineMap_apply] at hperp2
    linarith
  have hw : u 0 ≠ y 0 ∨ u 1 ≠ y 1 := by
    by_contra hc; push_neg at hc
    exact hne (by ext i; fin_cases i <;> [exact hc.1; exact hc.2])
  set w0 := u 0 - y 0; set w1 := u 1 - y 1
  set p0 := q 0 - v2 0; set p1 := q 1 - v2 1
  set p'0 := q 0 - (y 0 + u 0) / 2; set p'1 := q 1 - (y 1 + u 1) / 2
  have key2 : w0 * (p0 * p'1 - p1 * p'0) = 0 := by linear_combination p'1 * h1 - p1 * h2
  have key1 : w1 * (p0 * p'1 - p1 * p'0) = 0 := by linear_combination p0 * h2 - p'0 * h1
  have hcross : p0 * p'1 - p1 * p'0 = 0 := by
    rcases hw with h | h
    · exact (mul_eq_zero.mp key2).resolve_left (sub_ne_zero.mpr h)
    · exact (mul_eq_zero.mp key1).resolve_left (sub_ne_zero.mpr h)
  have hm0 : (midpoint ℝ y u) 0 = (y 0 + u 0) / 2 := by
    simp [midpoint, AffineMap.lineMap_apply]; ring
  have hm1 : (midpoint ℝ y u) 1 = (y 1 + u 1) / 2 := by
    simp [midpoint, AffineMap.lineMap_apply]; ring
  simp only [signedArea2, hm0, hm1]
  simp only [p0, p1, p'0, p'1] at hcross
  linarith
theorem signedArea2_apex_midpoint (q v2 y u : ℝ²) :
    2 * signedArea2 (midpoint ℝ y u) q v2 = signedArea2 y q v2 + signedArea2 u q v2 := by
  have hm0 : (midpoint ℝ y u) 0 = (y 0 + u 0) / 2 := by
    rw [midpoint_eq_smul_add]; simp; ring
  have hm1 : (midpoint ℝ y u) 1 = (y 1 + u 1) / 2 := by
    rw [midpoint_eq_smul_add]; simp; ring
  simp only [signedArea2, hm0, hm1]; ring
theorem signedArea2_reflection_neg {q v2 y u : ℝ²}
    (hmid : signedArea2 (midpoint ℝ y u) q v2 = 0) :
    signedArea2 u q v2 = - signedArea2 y q v2 := by
  have h := signedArea2_apex_midpoint q v2 y u
  rw [hmid] at h; linarith
end Problem97
end Batch3N9
end Batch3N9Unit049

section Batch3N9SingleApexCircleSupport
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open EuclideanGeometry Finset
namespace Problem97
namespace FiniteEndpointShell
theorem k4_at_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Erdos97.HasNEquidistantPointsAt 4 A S.triangle.v1 :=
  S.hK4 _ S.triangle.v1_mem

theorem k4_at_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Erdos97.HasNEquidistantPointsAt 4 A S.triangle.v2 :=
  S.hK4 _ S.triangle.v2_mem

theorem k4_at_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Erdos97.HasNEquidistantPointsAt 4 A S.triangle.v3 :=
  S.hK4 _ S.triangle.v3_mem

theorem n5_forced_m44
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    S.CP.C1.card = 4 ∧ S.CP.C2.card = 4 ∧ S.CP.C3.card = 4 := by
  have hC1ge : 4 ≤ S.CP.C1.card := by
    rcases S.k4_at_v1 with ⟨r, hr, hcard⟩
    exact le_trans hcard (Finset.card_le_card (hN4e.1 hr hcard))
  have hC2ge : 4 ≤ S.CP.C2.card := by
    rcases S.k4_at_v2 with ⟨r, hr, hcard⟩
    exact le_trans hcard (Finset.card_le_card (hN4e.2.1 hr hcard))
  have hC3ge : 4 ≤ S.CP.C3.card := by
    rcases S.k4_at_v3 with ⟨r, hr, hcard⟩
    exact le_trans hcard (Finset.card_le_card (hN4e.2.2 hr hcard))
  have hsum := S.hcapSum12
  omega

theorem exact_cap_class_at_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    ∃ r : ℝ, 0 < r ∧
      A.filter (fun x => dist S.triangle.v1 x = r) = S.CP.C1 := by
  classical
  rcases S.k4_at_v1 with ⟨r, hr, hcard⟩
  let T : Finset ℝ² := A.filter (fun x => dist S.triangle.v1 x = r)
  have hTfour : 4 ≤ T.card := by
    simpa [T, triangle, Problem97.MEC.MoserTriangle.toStructural] using hcard
  have hsub : T ⊆ S.CP.C1 := hN4e.1 hr hTfour
  have hcap4 : S.CP.C1.card = 4 := (S.n5_forced_m44 hN4e).1
  have hcle : S.CP.C1.card ≤ T.card := by
    omega
  refine ⟨r, hr, ?_⟩
  exact Finset.eq_of_subset_of_card_le hsub hcle

theorem exact_cap_class_at_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    ∃ r : ℝ, 0 < r ∧
      A.filter (fun x => dist S.triangle.v2 x = r) = S.CP.C2 := by
  classical
  rcases S.k4_at_v2 with ⟨r, hr, hcard⟩
  let T : Finset ℝ² := A.filter (fun x => dist S.triangle.v2 x = r)
  have hTfour : 4 ≤ T.card := by
    simpa [T, triangle, Problem97.MEC.MoserTriangle.toStructural] using hcard
  have hsub : T ⊆ S.CP.C2 := hN4e.2.1 hr hTfour
  have hcap4 : S.CP.C2.card = 4 := (S.n5_forced_m44 hN4e).2.1
  have hcle : S.CP.C2.card ≤ T.card := by
    omega
  refine ⟨r, hr, ?_⟩
  exact Finset.eq_of_subset_of_card_le hsub hcle

theorem exact_cap_class_at_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) :
    ∃ r : ℝ, 0 < r ∧
      A.filter (fun x => dist S.triangle.v3 x = r) = S.CP.C3 := by
  classical
  rcases S.k4_at_v3 with ⟨r, hr, hcard⟩
  let T : Finset ℝ² := A.filter (fun x => dist S.triangle.v3 x = r)
  have hTfour : 4 ≤ T.card := by
    simpa [T, triangle, Problem97.MEC.MoserTriangle.toStructural] using hcard
  have hsub : T ⊆ S.CP.C3 := hN4e.2.2 hr hTfour
  have hcap4 : S.CP.C3.card = 4 := (S.n5_forced_m44 hN4e).2.2
  have hcle : S.CP.C3.card ≤ T.card := by
    omega
  refine ⟨r, hr, ?_⟩
  exact Finset.eq_of_subset_of_card_le hsub hcle
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9SingleApexCircleSupport

section Batch3N9SingleApexShellSupport
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open EuclideanGeometry Finset
namespace Problem97
namespace FiniteEndpointShell
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
    simpa [T, triangle, Problem97.MEC.MoserTriangle.toStructural] using hTcard
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
    simpa [T, triangle, Problem97.MEC.MoserTriangle.toStructural] using hTcard
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
    simpa [T, triangle, Problem97.MEC.MoserTriangle.toStructural] using hTcard
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
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9SingleApexShellSupport

section Batch3N9SingleApexArcAngleSupport
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open EuclideanGeometry Finset
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
end Batch3N9SingleApexArcAngleSupport

section Batch3N9SingleApexArcInteriorSupport
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open EuclideanGeometry Finset
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
end Batch3N9SingleApexArcInteriorSupport

-- Original module: Solutions.Batch3N9.WitnessPacketInterface
section Batch3N9Unit074
namespace Batch3N9
open scoped EuclideanGeometry
open EuclideanGeometry
namespace Problem97
noncomputable def SelectedClass (A : Finset ℝ²) (s : ℝ²) (d : ℝ) : Finset ℝ² :=
  A.filter (fun q => dist s q = d)
@[simp] theorem mem_selectedClass {A : Finset ℝ²} {s : ℝ²} {d : ℝ} {q : ℝ²} :
    q ∈ SelectedClass A s d ↔ q ∈ A ∧ dist s q = d := by
  simp [SelectedClass]
theorem exists_selectedClass_card_ge_of_hasNEquidistantPointsAt
    {n : ℕ} {A : Finset ℝ²} {p : ℝ²}
    (h : HasNEquidistantPointsAt n A p) :
    ∃ r : ℝ, 0 < r ∧ n ≤ (SelectedClass A p r).card := by
  rcases h with ⟨r, hr, hcard⟩
  exact ⟨r, hr, by simpa [SelectedClass] using hcard⟩
theorem exists_selectedClass_card_ge_four_of_hasNEquidistantProperty
    {A : Finset ℝ²} {p : ℝ²}
    (hK4 : HasNEquidistantProperty 4 A) (hp : p ∈ A) :
    ∃ r : ℝ, 0 < r ∧ 4 ≤ (SelectedClass A p r).card :=
  exists_selectedClass_card_ge_of_hasNEquidistantPointsAt (hK4 p hp)
theorem dist_self_of_mem_selectedClass {A : Finset ℝ²} {s q : ℝ²} {d : ℝ}
    (hq : q ∈ SelectedClass A s d) : dist q s = d :=
  (dist_comm q s).trans (mem_selectedClass.mp hq).2
end Problem97
end Batch3N9
end Batch3N9Unit074

-- Original module: Solutions.Batch3N9.U2.OneHitBound
section Batch3N9Unit075
namespace Batch3N9
open scoped EuclideanGeometry
open EuclideanGeometry
namespace Problem97
abbrev N8a3AdjacentCapDistanceStrict
    (center : ℝ²) {m : ℕ} (L : FiniteEndpoint.OrderedSideChain m) : Prop :=
  ∀ {i j : Fin m}, i < j → dist center (L.points i) < dist center (L.points j)
end Problem97
end Batch3N9
end Batch3N9Unit075

-- Original module: Solutions.Batch3N9.U2.OneHitMonotone
section Batch3N9Unit076
set_option backward.isDefEq.respectTransparency false
namespace Batch3N9
open Real Set
open scoped EuclideanGeometry
namespace Problem97
noncomputable def pt (x y : ℝ) : ℝ² := !₂[x, y]
noncomputable def capU1 (α : ℝ) : ℝ² := pt (Real.cos α) (Real.sin α)
noncomputable def capU2 (γ : ℝ) : ℝ² := pt (1 + Real.cos (2*π/3 + γ)) (Real.sin (2*π/3 + γ))
theorem capU1U2_dist_sq (α γ : ℝ) :
    dist (capU1 α) (capU2 γ) ^ 2
      = 3 - 2 * Real.cos α - 2 * Real.cos (α - 2*π/3 - γ) + 2 * Real.cos (2*π/3 + γ) := by
  have norm_sub_sq : ∀ (a b : ℝ²),
      dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 :=
    Problem97.dist_sq_coord
  rw [norm_sub_sq]
  simp only [capU1, capU2, pt, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcos_sub : Real.cos (α - 2*π/3 - γ)
      = Real.cos α * Real.cos (2*π/3 + γ) + Real.sin α * Real.sin (2*π/3 + γ) := by
    rw [show α - 2*π/3 - γ = α - (2*π/3 + γ) by ring, Real.cos_sub]
  rw [hcos_sub]
  nlinarith only [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq (2*π/3 + γ)]
theorem capU1U2_dist_sq_strictMonoOn {α : ℝ} (hα0 : 0 < α) (hα1 : α < π/3) :
    StrictMonoOn (fun γ => dist (capU1 α) (capU2 γ) ^ 2) (Set.Icc 0 (π/3)) := by
  have key : (fun γ => dist (capU1 α) (capU2 γ) ^ 2)
      = (fun γ => 3 - 2 * Real.cos α - 2 * Real.cos (α - 2*π/3 - γ)
          + 2 * Real.cos (2*π/3 + γ)) := by
    funext γ; exact capU1U2_dist_sq α γ
  rw [key]
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (π/3))
  · fun_prop
  · intro γ hγ
    rw [interior_Icc] at hγ
    obtain ⟨hγ0, hγ1⟩ := hγ
    have hd : HasDerivAt
        (fun γ => 3 - 2 * Real.cos α - 2 * Real.cos (α - 2*π/3 - γ)
          + 2 * Real.cos (2*π/3 + γ))
        (-2 * Real.sin (α - 2*π/3 - γ) - 2 * Real.sin (2*π/3 + γ)) γ := by
      have h1 : HasDerivAt (fun γ : ℝ => α - 2*π/3 - γ) (-1) γ := by
        simpa using (hasDerivAt_id γ).const_sub (α - 2*π/3)
      have h2 : HasDerivAt (fun γ : ℝ => 2*π/3 + γ) (1) γ := by
        simpa using (hasDerivAt_id γ).const_add (2*π/3)
      have c1 := (h1.cos).const_mul (2 : ℝ)
      have c2 := (h2.cos).const_mul (2 : ℝ)
      have := ((hasDerivAt_const γ (3 - 2 * Real.cos α)).sub c1).add c2
      convert this using 1 <;> (first | rfl | ring)
    rw [hd.deriv]
    have hprod : -2 * Real.sin (α - 2*π/3 - γ) - 2 * Real.sin (2*π/3 + γ)
        = -4 * Real.sin (α/2) * Real.cos (2*π/3 + γ - α/2) := by
      have hsum := Real.sin_add_sin (α - 2*π/3 - γ) (2*π/3 + γ)
      have e1 : (α - 2*π/3 - γ + (2*π/3 + γ)) / 2 = α/2 := by ring
      have e2 : (α - 2*π/3 - γ - (2*π/3 + γ)) / 2 = -(2*π/3 + γ - α/2) := by ring
      rw [e1, e2, Real.cos_neg] at hsum; nlinarith only [hsum]
    rw [hprod]
    have hsin : 0 < Real.sin (α/2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hcos : Real.cos (2*π/3 + γ - α/2) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
    nlinarith only [hsin, hcos]
theorem capU2_dist_strictMonoOn {α : ℝ} (hα0 : 0 < α) (hα1 : α < π/3) :
    StrictMonoOn (fun γ => dist (capU1 α) (capU2 γ)) (Set.Icc 0 (π/3)) := by
  intro a ha b hb hab
  exact lt_of_pow_lt_pow_left₀ 2 dist_nonneg (capU1U2_dist_sq_strictMonoOn hα0 hα1 ha hb hab)
noncomputable def capU3 (δ : ℝ) : ℝ² :=
  pt (1/2 + Real.cos (4*π/3 + δ)) (Real.sqrt 3 / 2 + Real.sin (4*π/3 + δ))
theorem capU1U3_dist_sq (α δ : ℝ) :
    dist (capU1 α) (capU3 δ) ^ 2
      = 3 - Real.cos α - Real.sqrt 3 * Real.sin α
          - 2 * Real.cos (α - 4*π/3 - δ) + Real.cos (4*π/3 + δ)
          + Real.sqrt 3 * Real.sin (4*π/3 + δ) := by
  have norm_sub_sq : ∀ (a b : ℝ²),
      dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 :=
    Problem97.dist_sq_coord
  rw [norm_sub_sq]
  simp only [capU1, capU3, pt, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcos_sub : Real.cos (α - 4*π/3 - δ)
      = Real.cos α * Real.cos (4*π/3 + δ) + Real.sin α * Real.sin (4*π/3 + δ) := by
    rw [show α - 4*π/3 - δ = α - (4*π/3 + δ) by ring, Real.cos_sub]
  rw [hcos_sub]
  linear_combination Real.sin_sq_add_cos_sq α + Real.sin_sq_add_cos_sq (4*π/3 + δ)
    + (1/4) * Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
theorem capU1U3_dist_sq_strictAntiOn {α : ℝ} (hα0 : 0 < α) (hα1 : α < π/3) :
    StrictAntiOn (fun δ => dist (capU1 α) (capU3 δ) ^ 2) (Set.Icc 0 (π/3)) := by
  have key : (fun δ => dist (capU1 α) (capU3 δ) ^ 2)
      = (fun δ => 3 - Real.cos α - Real.sqrt 3 * Real.sin α
          - 2 * Real.cos (α - 4*π/3 - δ) + Real.cos (4*π/3 + δ)
          + Real.sqrt 3 * Real.sin (4*π/3 + δ)) := by
    funext δ; exact capU1U3_dist_sq α δ
  rw [key]
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 (π/3))
  · fun_prop
  · intro δ hδ
    rw [interior_Icc] at hδ
    obtain ⟨hδ0, hδ1⟩ := hδ
    have hd : HasDerivAt
        (fun δ => 3 - Real.cos α - Real.sqrt 3 * Real.sin α
          - 2 * Real.cos (α - 4*π/3 - δ) + Real.cos (4*π/3 + δ)
          + Real.sqrt 3 * Real.sin (4*π/3 + δ))
        (-2 * Real.sin (α - 4*π/3 - δ) - Real.sin (4*π/3 + δ)
          + Real.sqrt 3 * Real.cos (4*π/3 + δ)) δ := by
      have h1 : HasDerivAt (fun δ : ℝ => α - 4*π/3 - δ) (-1) δ := by
        simpa using (hasDerivAt_id δ).const_sub (α - 4*π/3)
      have h2 : HasDerivAt (fun δ : ℝ => 4*π/3 + δ) (1) δ := by
        simpa using (hasDerivAt_id δ).const_add (4*π/3)
      have hbase : HasDerivAt
          (fun _ : ℝ => (3:ℝ) - Real.cos α - Real.sqrt 3 * Real.sin α) 0 δ :=
        hasDerivAt_const δ _
      have t1 := (h1.cos).const_mul (2 : ℝ)
      have t2 := h2.cos
      have t3 := (h2.sin).const_mul (Real.sqrt 3)
      have := ((hbase.sub t1).add t2).add t3
      convert this using 1 <;> (first | rfl | ring)
    rw [hd.deriv]
    have hsp := Real.sin_sub_sin δ (α - 4*π/3 - δ)
    rw [show (δ - (α - 4*π/3 - δ)) / 2 = 2*π/3 + δ - α/2 by ring,
        show (δ + (α - 4*π/3 - δ)) / 2 = α/2 - 2*π/3 by ring] at hsp
    have hstep : -Real.sin (4*π/3 + δ) + Real.sqrt 3 * Real.cos (4*π/3 + δ)
        = 2 * Real.sin δ := by
      have hc43 : Real.cos (4*π/3) = -(1/2) := by
        rw [show (4:ℝ)*π/3 = π + π/3 by ring, Real.cos_add, Real.cos_pi, Real.sin_pi,
            Real.cos_pi_div_three]; ring
      have hs43 : Real.sin (4*π/3) = -(Real.sqrt 3 / 2) := by
        rw [show (4:ℝ)*π/3 = π + π/3 by ring, Real.sin_add, Real.cos_pi, Real.sin_pi,
            Real.sin_pi_div_three]; ring
      rw [Real.sin_add, Real.cos_add, hc43, hs43]
      linear_combination (Real.sin δ / 2) * Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    have hD : -2 * Real.sin (α - 4*π/3 - δ) - Real.sin (4*π/3 + δ)
          + Real.sqrt 3 * Real.cos (4*π/3 + δ)
        = 4 * Real.cos (α/2 - 2*π/3) * Real.sin (2*π/3 + δ - α/2) := by
      linear_combination 2 * hsp + hstep
    rw [hD]
    have hcos : Real.cos (α/2 - 2*π/3) < 0 := by
      rw [show α/2 - 2*π/3 = -(2*π/3 - α/2) by ring, Real.cos_neg]
      exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
    have hsin : 0 < Real.sin (2*π/3 + δ - α/2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    nlinarith only [hcos, hsin]
theorem capU3_dist_strictAntiOn {α : ℝ} (hα0 : 0 < α) (hα1 : α < π/3) :
    StrictAntiOn (fun δ => dist (capU1 α) (capU3 δ)) (Set.Icc 0 (π/3)) := by
  intro a ha b hb hab
  exact lt_of_pow_lt_pow_left₀ 2 dist_nonneg
    (capU1U3_dist_sq_strictAntiOn hα0 hα1 ha hb hab)
end Problem97
end Batch3N9
end Batch3N9Unit076

-- Original module: Solutions.Batch3N9.U2.OneHitRealization
section Batch3N9Unit077
namespace Batch3N9
open Real Set
open scoped EuclideanGeometry
namespace Problem97
theorem n8a3_of_distScalingToCapU2
    {T : ℝ² → ℝ²} {scale : ℝ} (hscale : 0 < scale)
    (hdist : ∀ a b : ℝ², dist (T a) (T b) = scale * dist a b)
    {s : ℝ²} {m : ℕ} (L : FiniteEndpoint.OrderedSideChain m)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < π/3)
    (γ : Fin m → ℝ) (hγmem : ∀ i, γ i ∈ Set.Icc (0:ℝ) (π/3)) (hγmono : StrictMono γ)
    (hs : T s = capU1 α)
    (hL : ∀ i, T (L.points i) = capU2 (γ i)) :
    N8a3AdjacentCapDistanceStrict s L := by
  intro i j hij
  have hmono := capU2_dist_strictMonoOn hα0 hα1 (hγmem i) (hγmem j) (hγmono hij)
  simp only [] at hmono
  rw [← hs, ← hL i, ← hL j, hdist, hdist] at hmono
  nlinarith only [hmono, hscale]
theorem n8a3_of_distScalingToCapU3
    {T : ℝ² → ℝ²} {scale : ℝ} (hscale : 0 < scale)
    (hdist : ∀ a b : ℝ², dist (T a) (T b) = scale * dist a b)
    {s : ℝ²} {m : ℕ} (L : FiniteEndpoint.OrderedSideChain m)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < π/3)
    (δ : Fin m → ℝ) (hδmem : ∀ i, δ i ∈ Set.Icc (0:ℝ) (π/3)) (hδanti : StrictAnti δ)
    (hs : T s = capU1 α)
    (hL : ∀ i, T (L.points i) = capU3 (δ i)) :
    N8a3AdjacentCapDistanceStrict s L := by
  intro i j hij
  have hmono := capU3_dist_strictAntiOn hα0 hα1 (hδmem j) (hδmem i) (hδanti hij)
  simp only [] at hmono
  rw [← hs, ← hL i, ← hL j, hdist, hdist] at hmono
  nlinarith only [hmono, hscale]
end Problem97
end Batch3N9
end Batch3N9Unit077

-- Original module: Solutions.Batch3N9.N8.N8aArcTwoCircle
section Batch3N9Unit078
namespace Batch3N9
open scoped EuclideanGeometry
open EuclideanGeometry
namespace Problem97
structure N8ArcCircle where
  support : Finset ℝ²
  circleCenter : ℝ²
  circleRadius : ℝ
  on_circle : ∀ x ∈ support, dist circleCenter x = circleRadius
namespace N8ArcCircle
theorem mem_sphere (P : N8ArcCircle) {x : ℝ²} (hx : x ∈ P.support) :
    x ∈ (⟨P.circleCenter, P.circleRadius⟩ : Sphere ℝ²) := by
  exact EuclideanGeometry.mem_sphere.mpr <| by
    calc
      dist x P.circleCenter = dist P.circleCenter x := dist_comm x P.circleCenter
      _ = P.circleRadius := P.on_circle x hx
end N8ArcCircle
structure N8ApexArcWitness where
  apex : ℝ²
  selectedRadius : ℝ
  arc : N8ArcCircle
  circles_ne : (⟨apex, selectedRadius⟩ : Sphere ℝ²) ≠
    ⟨arc.circleCenter, arc.circleRadius⟩
structure N8AdjacentArcWitness where
  base : N8ApexArcWitness
  m : ℕ
  chain : FiniteEndpoint.OrderedSideChain m
  chain_covers : base.arc.support ⊆ chain.support
  monotone : N8a3AdjacentCapDistanceStrict base.apex chain
namespace N8ApexArcWitness
end N8ApexArcWitness
namespace N8AdjacentArcWitness
theorem selectedClass_inter_card_le_one
    {A : Finset ℝ²} (W : N8AdjacentArcWitness) :
    ((SelectedClass A W.base.apex W.base.selectedRadius) ∩ W.base.arc.support).card ≤ 1 := by
  apply FiniteEndpoint.OrderedSideChain.card_le_one_of_subset_sameRadius
      W.base.apex W.chain W.monotone W.base.selectedRadius
  · intro x hx
    exact W.chain_covers (Finset.mem_of_mem_inter_right hx)
  · intro x hx
    exact (mem_selectedClass.mp (Finset.mem_of_mem_inter_left hx)).2
end N8AdjacentArcWitness
namespace FiniteEndpointShell
theorem N8a3_adjacent_one_hit
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (_hN4e : S.N4eCapContainment)
    (hadj : N8AdjacentArcWitness) :
    ((SelectedClass A hadj.base.apex hadj.base.selectedRadius) ∩
      hadj.base.arc.support).card ≤ 1 := by
  exact hadj.selectedClass_inter_card_le_one
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit078

-- Original module: Solutions.Batch3N9.N8.N8bEndpointPair
section Batch3N9Unit079
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
theorem capInteriorByIndex_subset
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) :
    S.capInteriorByIndex i ⊆ A := by
  intro x hx
  fin_cases i
  · simp only [capInteriorByIndex] at hx
    rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hx
    exact S.CP.C1_subset hx.2.2
  · simp only [capInteriorByIndex] at hx
    rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hx
    exact S.CP.C2_subset hx.2.2
  · simp only [capInteriorByIndex] at hx
    rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hx
    exact S.CP.C3_subset hx.2.2
@[reducible] def ownLeftEndpointByIndex
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) : ℝ² :=
  match i.1 with
  | 0 => S.triangle.v2
  | 1 => S.triangle.v3
  | _ => S.triangle.v1
@[reducible] def ownRightEndpointByIndex
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) : ℝ² :=
  match i.1 with
  | 0 => S.triangle.v3
  | 1 => S.triangle.v1
  | _ => S.triangle.v2
@[reducible] noncomputable def leftAdjacentInteriorByIndex
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) : Finset ℝ² :=
  match i.1 with
  | 0 => S.I2
  | 1 => S.I3
  | _ => S.I1
@[reducible] noncomputable def rightAdjacentInteriorByIndex
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) : Finset ℝ² :=
  match i.1 with
  | 0 => S.I3
  | 1 => S.I1
  | _ => S.I2
structure N8SelectedApex
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) (x : ℝ²) where
  radius : ℝ
  radius_pos : 0 < radius
  cap_mem : x ∈ S.capInteriorByIndex i
  selected_card : 4 ≤ (SelectedClass A x radius).card
theorem N8SelectedApex.nonempty_of_hasNEquidistantProperty
    {A : Finset ℝ²} {S : FiniteEndpointShell A} {i : Fin 3} {x : ℝ²}
    (hK4 : HasNEquidistantProperty 4 A)
    (hxcap : x ∈ S.capInteriorByIndex i) :
    Nonempty (N8SelectedApex S i x) := by
  have hxA : x ∈ A := S.capInteriorByIndex_subset i hxcap
  rcases exists_selectedClass_card_ge_four_of_hasNEquidistantProperty hK4 hxA with
    ⟨r, hr, hcard⟩
  exact ⟨{ radius := r
           radius_pos := hr
           cap_mem := hxcap
           selected_card := hcard }⟩
structure N8MoserEndpointPair
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) (x : ℝ²) (radius : ℝ) where
  m₁ : ℝ²
  m₂ : ℝ²
  m₁_moser : m₁ ∈ S.triangle.verts
  m₂_moser : m₂ ∈ S.triangle.verts
  m₁_mem : m₁ ∈ SelectedClass A x radius
  m₂_mem : m₂ ∈ SelectedClass A x radius
  m₁_ne_m₂ : m₁ ≠ m₂
theorem mem_oppositeCap_of_selected
    {A : Finset ℝ²}
    {x va ve w : ℝ²} {radius d r : ℝ}
    (hxA : x ∈ A) {Ce : Finset ℝ²}
    (hdist_va_x : dist va x = d)
    (hva_mem : va ∈ SelectedClass A x radius)
    (hve_mem : ve ∈ SelectedClass A x radius)
    (hCeEq : A.filter (fun y => dist ve y = r) = Ce)
    (hw_mem : w ∈ Ce) (hw_dist : dist ve w = d) :
    x ∈ Ce := by
  classical
  have hxva : dist x va = radius := (mem_selectedClass.mp hva_mem).2
  have hrad : radius = d := by rw [← hxva, dist_comm]; exact hdist_va_x
  have hxve : dist x ve = radius := (mem_selectedClass.mp hve_mem).2
  have hdist_ve_x : dist ve x = d := by rw [dist_comm, hxve, hrad]
  have hw_filter : w ∈ A.filter (fun y => dist ve y = r) := by rw [hCeEq]; exact hw_mem
  have hrd : r = d := by rw [← hw_dist]; exact ((Finset.mem_filter.mp hw_filter).2).symm
  rw [← hCeEq, Finset.mem_filter]
  exact ⟨hxA, by rw [hrd]; exact hdist_ve_x⟩
theorem two_caps_nonmoser_false_12
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {x : ℝ²}
    (hxA : x ∈ A) (hxnon : x ∉ S.triangle.verts)
    (h1 : x ∈ S.CP.C1) (h2 : x ∈ S.CP.C2) : False := by
  have h := S.CP.nonmoser_in_one x hxA hxnon
  rw [if_pos h1, if_pos h2] at h; split at h <;> omega
theorem two_caps_nonmoser_false_13
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {x : ℝ²}
    (hxA : x ∈ A) (hxnon : x ∉ S.triangle.verts)
    (h1 : x ∈ S.CP.C1) (h3 : x ∈ S.CP.C3) : False := by
  have h := S.CP.nonmoser_in_one x hxA hxnon
  rw [if_pos h1, if_pos h3] at h; split at h <;> omega
theorem two_caps_nonmoser_false_23
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {x : ℝ²}
    (hxA : x ∈ A) (hxnon : x ∉ S.triangle.verts)
    (h2 : x ∈ S.CP.C2) (h3 : x ∈ S.CP.C3) : False := by
  have h := S.CP.nonmoser_in_one x hxA hxnon
  rw [if_pos h2, if_pos h3] at h; split at h <;> omega
theorem nonOwnPair_index_false
    {A : Finset ℝ²}
    {x va vb vc : ℝ²} {radius : ℝ}
    {m₁ m₂ : ℝ²}
    (hm₁ : m₁ = va ∨ m₁ = vb ∨ m₁ = vc) (hm₂ : m₂ = va ∨ m₂ = vb ∨ m₂ = vc)
    (hne : m₁ ≠ m₂)
    (hown : ¬((m₁ = vb ∧ m₂ = vc) ∨ (m₁ = vc ∧ m₂ = vb)))
    (hm₁mem : m₁ ∈ SelectedClass A x radius) (hm₂mem : m₂ ∈ SelectedClass A x radius)
    (hContraB : va ∈ SelectedClass A x radius → vb ∈ SelectedClass A x radius → False)
    (hContraC : va ∈ SelectedClass A x radius → vc ∈ SelectedClass A x radius → False) :
    False := by
  classical
  rcases hm₁ with rfl | rfl | rfl <;> rcases hm₂ with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | exact hContraB hm₁mem hm₂mem
    | exact hContraB hm₂mem hm₁mem
    | exact hContraC hm₁mem hm₂mem
    | exact hContraC hm₂mem hm₁mem
    | exact hown (Or.inl ⟨rfl, rfl⟩)
    | exact hown (Or.inr ⟨rfl, rfl⟩)
theorem N8b_endpoint_pair_split
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment)
    {x : ℝ²} {i : Fin 3}
    (hx : N8SelectedApex S i x)
    (hMoser2 : N8MoserEndpointPair S i x hx.radius)
    (hnotown : ¬((hMoser2.m₁ = S.ownLeftEndpointByIndex i ∧
                  hMoser2.m₂ = S.ownRightEndpointByIndex i) ∨
                 (hMoser2.m₁ = S.ownRightEndpointByIndex i ∧
                  hMoser2.m₂ = S.ownLeftEndpointByIndex i))) :
    False := by
  classical
  obtain ⟨m₁, m₂, m₁_moser, m₂_moser, m₁_mem, m₂_mem, m₁_ne_m₂⟩ := hMoser2
  have hown : ¬((m₁ = S.ownLeftEndpointByIndex i ∧ m₂ = S.ownRightEndpointByIndex i) ∨
               (m₁ = S.ownRightEndpointByIndex i ∧ m₂ = S.ownLeftEndpointByIndex i)) :=
    hnotown
  classical
    obtain ⟨d, hdpos, hC1d, hC2d, hC3d⟩ := Erdos9796FiniteNine.circle_placement S hN4e
    obtain ⟨r1, hr1, hC1eq⟩ := S.exact_cap_class_at_v1 hN4e
    obtain ⟨r2, hr2, hC2eq⟩ := S.exact_cap_class_at_v2 hN4e
    obtain ⟨r3, hr3, hC3eq⟩ := S.exact_cap_class_at_v3 hN4e
    have hm₁v : m₁ = S.triangle.v1 ∨ m₁ = S.triangle.v2 ∨ m₁ = S.triangle.v3 := by
      simpa only [MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
        using m₁_moser
    have hm₂v : m₂ = S.triangle.v1 ∨ m₂ = S.triangle.v2 ∨ m₂ = S.triangle.v3 := by
      simpa only [MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
        using m₂_moser
    fin_cases i
    ·
      have hxI1 : x ∈ S.I1 := hx.cap_mem
      have hxC1 : x ∈ S.CP.C1 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxI1)
      have hxA : x ∈ A := S.CP.C1_subset hxC1
      have hxnon : x ∉ S.triangle.verts := by
        simp only [MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
        push_neg
        refine ⟨fun h => S.CP.v1_notin_C1 (h ▸ hxC1),
          (Finset.mem_erase.mp (Finset.mem_erase.mp hxI1).2).1,
          (Finset.mem_erase.mp hxI1).1⟩
      exact nonOwnPair_index_false (va := S.triangle.v1) (vb := S.triangle.v2)
        (vc := S.triangle.v3) hm₁v hm₂v m₁_ne_m₂ hown m₁_mem m₂_mem
        (fun hva hvb =>
          two_caps_nonmoser_false_12 S hxA hxnon hxC1
            (mem_oppositeCap_of_selected hxA (hC1d x hxC1) hva hvb hC2eq
              S.CP.v3_mem_C2 (hC2d _ S.CP.v3_mem_C2)))
        (fun hva hvc =>
          two_caps_nonmoser_false_13 S hxA hxnon hxC1
            (mem_oppositeCap_of_selected hxA (hC1d x hxC1) hva hvc hC3eq
              S.CP.v2_mem_C3 (hC3d _ S.CP.v2_mem_C3)))
    ·
      have hxI2 : x ∈ S.I2 := hx.cap_mem
      have hxC2 : x ∈ S.CP.C2 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxI2)
      have hxA : x ∈ A := S.CP.C2_subset hxC2
      have hxnon : x ∉ S.triangle.verts := by
        simp only [MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
        push_neg
        refine ⟨(Finset.mem_erase.mp hxI2).1,
          fun h => S.CP.v2_notin_C2 (h ▸ hxC2),
          (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1⟩
      have hm₁v' : m₁ = S.triangle.v2 ∨ m₁ = S.triangle.v3 ∨ m₁ = S.triangle.v1 := by
        rcases hm₁v with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      have hm₂v' : m₂ = S.triangle.v2 ∨ m₂ = S.triangle.v3 ∨ m₂ = S.triangle.v1 := by
        rcases hm₂v with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      exact nonOwnPair_index_false (va := S.triangle.v2) (vb := S.triangle.v3)
        (vc := S.triangle.v1)
        hm₁v' hm₂v' m₁_ne_m₂ hown m₁_mem m₂_mem
        (fun hva hvb =>
          two_caps_nonmoser_false_23 S hxA hxnon hxC2
            (mem_oppositeCap_of_selected hxA (hC2d x hxC2) hva hvb hC3eq
              S.CP.v1_mem_C3 (hC3d _ S.CP.v1_mem_C3)))
        (fun hva hvc =>
          two_caps_nonmoser_false_12 S hxA hxnon
            (mem_oppositeCap_of_selected hxA (hC2d x hxC2) hva hvc hC1eq
              S.CP.v3_mem_C1 (hC1d _ S.CP.v3_mem_C1)) hxC2)
    ·
      have hxI3 : x ∈ S.I3 := hx.cap_mem
      have hxC3 : x ∈ S.CP.C3 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxI3)
      have hxA : x ∈ A := S.CP.C3_subset hxC3
      have hxnon : x ∉ S.triangle.verts := by
        simp only [MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
        push_neg
        refine ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hxI3).2).1,
          (Finset.mem_erase.mp hxI3).1,
          fun h => S.CP.v3_notin_C3 (h ▸ hxC3)⟩
      have hm₁v' : m₁ = S.triangle.v3 ∨ m₁ = S.triangle.v1 ∨ m₁ = S.triangle.v2 := by
        rcases hm₁v with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
      have hm₂v' : m₂ = S.triangle.v3 ∨ m₂ = S.triangle.v1 ∨ m₂ = S.triangle.v2 := by
        rcases hm₂v with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
      exact nonOwnPair_index_false (va := S.triangle.v3) (vb := S.triangle.v1)
        (vc := S.triangle.v2)
        hm₁v' hm₂v' m₁_ne_m₂ hown m₁_mem m₂_mem
        (fun hva hvb =>
          two_caps_nonmoser_false_13 S hxA hxnon
            (mem_oppositeCap_of_selected hxA (hC3d x hxC3) hva hvb hC1eq
              S.CP.v2_mem_C1 (hC1d _ S.CP.v2_mem_C1)) hxC3)
        (fun hva hvc =>
          two_caps_nonmoser_false_23 S hxA hxnon
            (mem_oppositeCap_of_selected hxA (hC3d x hxC3) hva hvc hC2eq
              S.CP.v1_mem_C2 (hC2d _ S.CP.v1_mem_C2)) hxC3)
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit079

-- Original module: Solutions.Batch3N9.N8.FourSubpacket
/- Original per-file notice from N8/FourSubpacket.lean:
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
section Batch3N9Unit080
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit080

-- Original module: Solutions.Batch3N9.N8.N8hiSameCap
section Batch3N9Unit081
namespace Batch3N9
open scoped EuclideanGeometry
open EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
structure N8SameCapClassPacket
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) (x : ℝ²) (i : Fin 3) where
  center : ℝ²
  radius : ℝ
  radius_pos : 0 < radius
  x_on_selected_circle : dist x center = radius
structure N8iCapCenterPacket
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {hN4e : S.N4eCapContainment}
    {x : ℝ²} {i : Fin 3}
    (hx : S.N8SameCapClassPacket hN4e x i) where
  sameCapMate : ℝ²
  fullWidthPoint : ℝ²
  mate_on_selected_circle : dist sameCapMate hx.center = hx.radius
  ref_on_selected_circle : dist fullWidthPoint hx.center = hx.radius
  x_mate_eq_radius : dist x sameCapMate = hx.radius
  x_ref_eq_radius : dist x fullWidthPoint = hx.radius
  mate_open_width :
    |(arcAngle hx.center x - arcAngle hx.center sameCapMate).toReal| <
      Real.pi / 3
  ref_full_width :
    |(arcAngle hx.center x - arcAngle hx.center fullWidthPoint).toReal| =
      Real.pi / 3
theorem N8i_capcenter_fullwidth_false
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment)
    {x : ℝ²} {i : Fin 3}
    (hx : S.N8SameCapClassPacket hN4e x i)
    (hCapCenterMoser : S.N8iCapCenterPacket hx) :
    False := by
  have hsameWidth :
      |(arcAngle hx.center x - arcAngle hx.center hCapCenterMoser.sameCapMate).toReal| =
        |(arcAngle hx.center x - arcAngle hx.center hCapCenterMoser.fullWidthPoint).toReal| := by
    apply
      (arcAngle_chord_length_eq_iff
        hx.center hx.radius hx.radius_pos
        x hCapCenterMoser.sameCapMate hCapCenterMoser.fullWidthPoint
        hx.x_on_selected_circle
        hCapCenterMoser.mate_on_selected_circle
        hCapCenterMoser.ref_on_selected_circle).mp
    calc
      dist x hCapCenterMoser.sameCapMate = hx.radius := hCapCenterMoser.x_mate_eq_radius
      _ = dist x hCapCenterMoser.fullWidthPoint := hCapCenterMoser.x_ref_eq_radius.symm
  have hfull :
      |(arcAngle hx.center x - arcAngle hx.center hCapCenterMoser.sameCapMate).toReal| =
        Real.pi / 3 := by
    exact hsameWidth.trans hCapCenterMoser.ref_full_width
  linarith [hCapCenterMoser.mate_open_width, hfull, Real.pi_pos]
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit081

-- Original module: Solutions.Batch3N9.U2.SimilarityNormalization
section Batch3N9Unit082
namespace Batch3N9
open Real Set
open scoped EuclideanGeometry
namespace Problem97
noncomputable def normSim (p₁ p₂ x : ℝ²) : ℝ² :=
  pt (((x 0 - p₁ 0) * (p₂ 0 - p₁ 0) + (x 1 - p₁ 1) * (p₂ 1 - p₁ 1))
        / ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2))
     (((x 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (x 0 - p₁ 0) * (p₂ 1 - p₁ 1))
        / ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2))
theorem b3n9m082_normSq_sub (u v : ℝ²) :
    dist u v ^ 2 = (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 :=
  Problem97.dist_sq_coord u v
theorem b3n9m082_normSim_ℓ2_pos {p₁ p₂ : ℝ²} (hp : p₁ ≠ p₂) :
    0 < (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := by
  have hd : 0 < dist p₁ p₂ := dist_pos.mpr hp
  have hsq : dist p₁ p₂ ^ 2 = (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := by
    rw [b3n9m082_normSq_sub]; ring
  nlinarith only [hsq, hd]
theorem normSim_dist_image (p₁ p₂ : ℝ²) (hp : p₁ ≠ p₂) (a b : ℝ²) :
    dist (normSim p₁ p₂ a) (normSim p₁ p₂ b) = (dist p₁ p₂)⁻¹ * dist a b := by
  have hℓ2 : (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 ≠ 0 := ne_of_gt (b3n9m082_normSim_ℓ2_pos hp)
  have hD : 0 < dist p₁ p₂ := dist_pos.mpr hp
  have hX : 0 ≤ dist (normSim p₁ p₂ a) (normSim p₁ p₂ b) := dist_nonneg
  have h2 : 0 ≤ (dist p₁ p₂)⁻¹ * dist a b :=
    mul_nonneg (inv_nonneg.mpr hD.le) dist_nonneg
  have hkey : dist (normSim p₁ p₂ a) (normSim p₁ p₂ b) ^ 2 * dist p₁ p₂ ^ 2
      = dist a b ^ 2 := by
    rw [b3n9m082_normSq_sub (normSim p₁ p₂ a) (normSim p₁ p₂ b), b3n9m082_normSq_sub p₁ p₂, b3n9m082_normSq_sub a b]
    simp only [normSim, pt, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have hsq : dist (normSim p₁ p₂ a) (normSim p₁ p₂ b) ^ 2
      = ((dist p₁ p₂)⁻¹ * dist a b) ^ 2 := by
    rw [mul_pow, inv_pow]
    field_simp
    linear_combination hkey
  rw [← Real.sqrt_sq hX, hsq, Real.sqrt_sq h2]
theorem normSim_fst (p₁ p₂ : ℝ²) : normSim p₁ p₂ p₁ = pt 0 0 := by
  simp only [normSim, pt, sub_self, zero_mul, add_zero, zero_div]
theorem normSim_snd (p₁ p₂ : ℝ²) (hp : p₁ ≠ p₂) : normSim p₁ p₂ p₂ = pt 1 0 := by
  have hℓ2 : (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 ≠ 0 := ne_of_gt (b3n9m082_normSim_ℓ2_pos hp)
  have e1 : ((p₂ 0 - p₁ 0) * (p₂ 0 - p₁ 0) + (p₂ 1 - p₁ 1) * (p₂ 1 - p₁ 1))
      / ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) = 1 := by
    rw [div_eq_iff hℓ2]; ring
  have e2 : ((p₂ 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (p₂ 0 - p₁ 0) * (p₂ 1 - p₁ 1))
      / ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) = 0 := by
    rw [div_eq_iff hℓ2]; ring
  rw [normSim, e1, e2]
theorem normSim_thd (p₁ p₂ p₃ : ℝ²) (hp : p₁ ≠ p₂)
    (h31 : dist p₁ p₂ = dist p₃ p₁) (h23 : dist p₁ p₂ = dist p₂ p₃)
    (hori : 0 < signedArea2 p₁ p₂ p₃) :
    normSim p₁ p₂ p₃ = pt (1 / 2) (Real.sqrt 3 / 2) := by
  have hℓ2 : 0 < (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := b3n9m082_normSim_ℓ2_pos hp
  have hℓ2' : (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 ≠ 0 := ne_of_gt hℓ2
  have eqA : (p₃ 0 - p₁ 0) ^ 2 + (p₃ 1 - p₁ 1) ^ 2
      = (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := by
    have h : dist p₃ p₁ ^ 2 = dist p₁ p₂ ^ 2 := by rw [h31]
    rw [b3n9m082_normSq_sub p₃ p₁, b3n9m082_normSq_sub p₁ p₂] at h; linear_combination h
  have eqB : (p₃ 0 - p₂ 0) ^ 2 + (p₃ 1 - p₂ 1) ^ 2
      = (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := by
    have h : dist p₂ p₃ ^ 2 = dist p₁ p₂ ^ 2 := by rw [h23]
    rw [b3n9m082_normSq_sub p₂ p₃, b3n9m082_normSq_sub p₁ p₂] at h; linear_combination h
  have hNX : 2 * ((p₃ 0 - p₁ 0) * (p₂ 0 - p₁ 0) + (p₃ 1 - p₁ 1) * (p₂ 1 - p₁ 1))
      = (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := by linear_combination eqA - eqB
  have hNY2 : ((p₃ 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (p₃ 0 - p₁ 0) * (p₂ 1 - p₁ 1)) ^ 2
      = 3 / 4 * ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) ^ 2 := by
    have ringid : ((p₃ 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (p₃ 0 - p₁ 0) * (p₂ 1 - p₁ 1)) ^ 2
        = ((p₃ 0 - p₁ 0) ^ 2 + (p₃ 1 - p₁ 1) ^ 2)
            * ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2)
          - ((p₃ 0 - p₁ 0) * (p₂ 0 - p₁ 0) + (p₃ 1 - p₁ 1) * (p₂ 1 - p₁ 1)) ^ 2 := by ring
    have hNXhalf : (p₃ 0 - p₁ 0) * (p₂ 0 - p₁ 0) + (p₃ 1 - p₁ 1) * (p₂ 1 - p₁ 1)
        = ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) / 2 := by linarith [hNX]
    rw [ringid, eqA, hNXhalf]; ring
  have hX : ((p₃ 0 - p₁ 0) * (p₂ 0 - p₁ 0) + (p₃ 1 - p₁ 1) * (p₂ 1 - p₁ 1))
      / ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) = 1 / 2 := by
    rw [div_eq_iff hℓ2']; linarith [hNX]
  have hNYpos : 0 < (p₃ 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (p₃ 0 - p₁ 0) * (p₂ 1 - p₁ 1) := by
    have heq : signedArea2 p₁ p₂ p₃
        = (p₃ 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (p₃ 0 - p₁ 0) * (p₂ 1 - p₁ 1) := by
      simp only [signedArea2]; ring
    rw [← heq]; exact hori
  have hsqrt3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hRHS : (0 : ℝ) ≤ Real.sqrt 3 / 2 * ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) := by
    positivity
  have hNYval : (p₃ 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (p₃ 0 - p₁ 0) * (p₂ 1 - p₁ 1)
      = Real.sqrt 3 / 2 * ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) := by
    have hsq : ((p₃ 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (p₃ 0 - p₁ 0) * (p₂ 1 - p₁ 1)) ^ 2
        = (Real.sqrt 3 / 2 * ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2)) ^ 2 := by
      rw [hNY2, mul_pow, div_pow, hsqrt3sq]; ring
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq hNYpos.le, Real.sqrt_sq hRHS] at this
  have hY : ((p₃ 1 - p₁ 1) * (p₂ 0 - p₁ 0) - (p₃ 0 - p₁ 0) * (p₂ 1 - p₁ 1))
      / ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2) = Real.sqrt 3 / 2 := by
    rw [div_eq_iff hℓ2', hNYval]
  simp only [normSim]
  rw [hX, hY]
theorem normSim_dist_fst (p₁ p₂ s : ℝ²) (hp : p₁ ≠ p₂) :
    dist (normSim p₁ p₂ s) (pt 0 0) = (dist p₁ p₂)⁻¹ * dist s p₁ := by
  rw [← normSim_fst p₁ p₂, normSim_dist_image p₁ p₂ hp s p₁]
theorem exists_capU1_of_dist_origin_one (q : ℝ²) (hq : dist q (pt 0 0) = 1) :
    ∃ α : ℝ, -π < α ∧ α ≤ π ∧ q = capU1 α := by
  have hcoord : (q 0) ^ 2 + (q 1) ^ 2 = 1 := by
    have h := b3n9m082_normSq_sub q (pt 0 0)
    rw [hq] at h
    simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero] at h
    nlinarith only [h]
  set z : ℂ := ⟨q 0, q 1⟩ with hz
  have hnsq : Complex.normSq z = 1 := by
    rw [hz, Complex.normSq_mk]; nlinarith only [hcoord]
  have habs : ‖z‖ = 1 := by rw [Complex.norm_def, hnsq, Real.sqrt_one]
  have hzne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at habs; exact one_ne_zero habs.symm
  refine ⟨z.arg, Complex.neg_pi_lt_arg z, Complex.arg_le_pi z, ?_⟩
  have hcos : Real.cos z.arg = q 0 := by
    rw [Complex.cos_arg hzne, habs, div_one]
  have hsin : Real.sin z.arg = q 1 := by
    rw [Complex.sin_arg, habs, div_one]
  rw [capU1, hcos, hsin]
  ext i
  fin_cases i <;> rfl
theorem signedArea2_normSim (p₁ p₂ : ℝ²) (hp : p₁ ≠ p₂) (a b c : ℝ²) :
    signedArea2 (normSim p₁ p₂ a) (normSim p₁ p₂ b) (normSim p₁ p₂ c)
      = ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2)⁻¹ * signedArea2 a b c := by
  have hL : (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 ≠ 0 := ne_of_gt (b3n9m082_normSim_ℓ2_pos hp)
  simp only [signedArea2, normSim, pt, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring
theorem capU1_arg_range (α : ℝ) (hlo : -π < α) (hhi : α ≤ π)
    (hC : signedArea2 (capU1 α) (pt 1 0) (pt (1 / 2) (Real.sqrt 3 / 2)) < 0) :
    0 < α ∧ α < π / 3 := by
  have hCeq : signedArea2 (capU1 α) (pt 1 0) (pt (1 / 2) (Real.sqrt 3 / 2))
      = Real.sqrt 3 / 2 - Real.cos (α - π / 6) := by
    simp only [signedArea2, capU1, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.cos_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]; ring
  rw [hCeq] at hC
  have hcos : Real.cos (π / 6) < Real.cos (α - π / 6) := by
    rw [Real.cos_pi_div_six]; linarith
  have h0 : (0 : ℝ) ≤ π / 6 := by positivity
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    rw [show α - π / 6 = -(π / 6 - α) by ring, Real.cos_neg] at hcos
    by_cases hb : π / 6 - α ≤ π
    · have hle : π / 6 ≤ π / 6 - α := by linarith
      have := Real.cos_le_cos_of_nonneg_of_le_pi h0 hb hle
      linarith
    · push_neg at hb
      have h1 : π / 2 ≤ π / 6 - α := by linarith [Real.pi_pos]
      have h2 : π / 6 - α ≤ π + π / 2 := by linarith
      have hnp := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
      have hp6 : (0 : ℝ) < Real.cos (π / 6) := by rw [Real.cos_pi_div_six]; positivity
      linarith
  · by_contra h
    push_neg at h
    have h2 : α - π / 6 ≤ π := by linarith
    have hle : π / 6 ≤ α - π / 6 := by linarith
    have := Real.cos_le_cos_of_nonneg_of_le_pi h0 h2 hle
    linarith
theorem normSim_centre_image (p₁ p₂ p₃ s : ℝ²) (hp : p₁ ≠ p₂)
    (h31 : dist p₁ p₂ = dist p₃ p₁) (h23 : dist p₁ p₂ = dist p₂ p₃)
    (hori : 0 < signedArea2 p₁ p₂ p₃)
    (hs1 : dist s p₁ = dist p₁ p₂)
    (hchord : signedArea2 s p₂ p₃ < 0) :
    ∃ α : ℝ, normSim p₁ p₂ s = capU1 α ∧ 0 < α ∧ α < π / 3 := by
  have hLpos : 0 < (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := b3n9m082_normSim_ℓ2_pos hp
  have h3img : normSim p₁ p₂ p₃ = pt (1 / 2) (Real.sqrt 3 / 2) :=
    normSim_thd p₁ p₂ p₃ hp h31 h23 hori
  have hone : dist (normSim p₁ p₂ s) (pt 0 0) = 1 := by
    rw [normSim_dist_fst p₁ p₂ s hp, hs1, inv_mul_cancel₀ (dist_ne_zero.mpr hp)]
  obtain ⟨α, hαlo, hαhi, hαeq⟩ := exists_capU1_of_dist_origin_one _ hone
  have hC : signedArea2 (capU1 α) (pt 1 0) (pt (1 / 2) (Real.sqrt 3 / 2)) < 0 := by
    have ht := signedArea2_normSim p₁ p₂ hp s p₂ p₃
    rw [hαeq, normSim_snd p₁ p₂ hp, h3img] at ht
    rw [ht]; exact mul_neg_of_pos_of_neg (inv_pos.mpr hLpos) hchord
  obtain ⟨hα0, hα1⟩ := capU1_arg_range α hαlo hαhi hC
  exact ⟨α, hαeq, hα0, hα1⟩
theorem exists_capU2_of_dist_v2_one (q : ℝ²) (hq : dist q (pt 1 0) = 1) :
    ∃ γ : ℝ, -(5 * π / 3) < γ ∧ γ ≤ π / 3 ∧ q = capU2 γ := by
  have hcoord : (q 0 - 1) ^ 2 + (q 1) ^ 2 = 1 := by
    have h := b3n9m082_normSq_sub q (pt 1 0)
    rw [hq] at h
    simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero] at h
    nlinarith only [h]
  set z : ℂ := ⟨q 0 - 1, q 1⟩ with hz
  have hnsq : Complex.normSq z = 1 := by
    rw [hz, Complex.normSq_mk]; nlinarith only [hcoord]
  have habs : ‖z‖ = 1 := by rw [Complex.norm_def, hnsq, Real.sqrt_one]
  have hzne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at habs; exact one_ne_zero habs.symm
  refine ⟨z.arg - 2 * π / 3, by have := Complex.neg_pi_lt_arg z; linarith,
    by have := Complex.arg_le_pi z; linarith, ?_⟩
  have hcos : Real.cos z.arg = q 0 - 1 := by rw [Complex.cos_arg hzne, habs, div_one]
  have hsin : Real.sin z.arg = q 1 := by rw [Complex.sin_arg, habs, div_one]
  have hq0 : q 0 = 1 + Real.cos (2 * π / 3 + (z.arg - 2 * π / 3)) := by
    rw [show 2 * π / 3 + (z.arg - 2 * π / 3) = z.arg by ring, hcos]; ring
  have hq1 : q 1 = Real.sin (2 * π / 3 + (z.arg - 2 * π / 3)) := by
    rw [show 2 * π / 3 + (z.arg - 2 * π / 3) = z.arg by ring, hsin]
  rw [capU2]
  ext i
  fin_cases i
  · simpa only [pt, Fin.mk_zero, Matrix.cons_val_zero] using hq0
  · simpa only [pt, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] using hq1
theorem capU2_arg_range (γ : ℝ) (hlo : -(5 * π / 3) < γ) (hhi : γ ≤ π / 3)
    (hC : signedArea2 (capU2 γ) (pt (1 / 2) (Real.sqrt 3 / 2)) (pt 0 0) < 0) :
    0 < γ ∧ γ < π / 3 := by
  have hCeq : signedArea2 (capU2 γ) (pt (1 / 2) (Real.sqrt 3 / 2)) (pt 0 0)
      = Real.sqrt 3 / 2 + Real.cos (5 * π / 6 + γ) := by
    rw [show (5 : ℝ) * π / 6 + γ = (2 * π / 3 + γ) + π / 6 by ring,
      Real.cos_add, Real.cos_pi_div_six, Real.sin_pi_div_six]
    simp only [signedArea2, capU2, pt, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hCeq] at hC
  have hcos2 : Real.cos (5 * π / 6 + γ) < -(Real.sqrt 3 / 2) := by linarith
  have c56 : Real.cos (5 * π / 6) = -(Real.sqrt 3 / 2) := by
    rw [show (5 : ℝ) * π / 6 = π - π / 6 by ring, Real.cos_sub, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_six]; ring
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    have hθhi : 5 * π / 6 + γ ≤ 5 * π / 6 := by linarith
    have habs : |5 * π / 6 + γ| ≤ 5 * π / 6 := by rw [abs_le]; constructor <;> linarith
    have hpi : 5 * π / 6 ≤ π := by linarith [Real.pi_pos]
    have := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi habs
    rw [Real.cos_abs, c56] at this
    linarith
  · by_contra h
    push_neg at h
    have hγ : γ = π / 3 := le_antisymm hhi h
    rw [hγ] at hcos2
    have c76 : Real.cos (5 * π / 6 + π / 3) = -(Real.sqrt 3 / 2) := by
      rw [show (5 : ℝ) * π / 6 + π / 3 = π + π / 6 by ring, Real.cos_add, Real.cos_pi,
        Real.sin_pi, Real.cos_pi_div_six]; ring
    rw [c76] at hcos2
    linarith
theorem normSim_chainImage_capU2 (p₁ p₂ p₃ w : ℝ²) (hp : p₁ ≠ p₂)
    (h31 : dist p₁ p₂ = dist p₃ p₁) (h23 : dist p₁ p₂ = dist p₂ p₃)
    (hori : 0 < signedArea2 p₁ p₂ p₃)
    (hw2 : dist w p₂ = dist p₁ p₂)
    (hchord : signedArea2 w p₃ p₁ < 0) :
    ∃ γ : ℝ, normSim p₁ p₂ w = capU2 γ ∧ 0 < γ ∧ γ < π / 3 := by
  have hLpos : 0 < (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := b3n9m082_normSim_ℓ2_pos hp
  have h3img : normSim p₁ p₂ p₃ = pt (1 / 2) (Real.sqrt 3 / 2) :=
    normSim_thd p₁ p₂ p₃ hp h31 h23 hori
  have hone : dist (normSim p₁ p₂ w) (pt 1 0) = 1 := by
    rw [← normSim_snd p₁ p₂ hp, normSim_dist_image p₁ p₂ hp w p₂, hw2,
      inv_mul_cancel₀ (dist_ne_zero.mpr hp)]
  obtain ⟨γ, hγlo, hγhi, hγeq⟩ := exists_capU2_of_dist_v2_one _ hone
  have hC : signedArea2 (capU2 γ) (pt (1 / 2) (Real.sqrt 3 / 2)) (pt 0 0) < 0 := by
    have ht := signedArea2_normSim p₁ p₂ hp w p₃ p₁
    rw [hγeq, h3img, normSim_fst p₁ p₂] at ht
    rw [ht]; exact mul_neg_of_pos_of_neg (inv_pos.mpr hLpos) hchord
  obtain ⟨hγ0, hγ1⟩ := capU2_arg_range γ hγlo hγhi hC
  exact ⟨γ, hγeq, hγ0, hγ1⟩
theorem exists_capU3_of_dist_v3_one (q : ℝ²) (hq : dist q (pt (1 / 2) (Real.sqrt 3 / 2)) = 1) :
    ∃ δ : ℝ, -(π / 3) < δ ∧ δ ≤ 5 * π / 3 ∧ q = capU3 δ := by
  have hcoord : (q 0 - 1 / 2) ^ 2 + (q 1 - Real.sqrt 3 / 2) ^ 2 = 1 := by
    have h := b3n9m082_normSq_sub q (pt (1 / 2) (Real.sqrt 3 / 2))
    rw [hq] at h
    simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    nlinarith only [h]
  set z : ℂ := ⟨q 0 - 1 / 2, q 1 - Real.sqrt 3 / 2⟩ with hz
  have hnsq : Complex.normSq z = 1 := by rw [hz, Complex.normSq_mk]; nlinarith only [hcoord]
  have habs : ‖z‖ = 1 := by rw [Complex.norm_def, hnsq, Real.sqrt_one]
  have hzne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at habs; exact one_ne_zero habs.symm
  refine ⟨z.arg + 2 * π / 3, by have := Complex.neg_pi_lt_arg z; linarith,
    by have := Complex.arg_le_pi z; linarith, ?_⟩
  have hcos : Real.cos z.arg = q 0 - 1 / 2 := by rw [Complex.cos_arg hzne, habs, div_one]
  have hsin : Real.sin z.arg = q 1 - Real.sqrt 3 / 2 := by rw [Complex.sin_arg, habs, div_one]
  have key : (4 : ℝ) * π / 3 + (z.arg + 2 * π / 3) = z.arg + 2 * π := by ring
  have hq0 : q 0 = 1 / 2 + Real.cos (4 * π / 3 + (z.arg + 2 * π / 3)) := by
    rw [key, Real.cos_add_two_pi, hcos]; ring
  have hq1 : q 1 = Real.sqrt 3 / 2 + Real.sin (4 * π / 3 + (z.arg + 2 * π / 3)) := by
    rw [key, Real.sin_add_two_pi, hsin]; ring
  rw [capU3]
  ext i
  fin_cases i
  · simpa only [pt, Fin.mk_zero, Matrix.cons_val_zero] using hq0
  · simpa only [pt, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] using hq1
theorem capU3_arg_range (δ : ℝ) (hlo : -(π / 3) < δ) (hhi : δ ≤ 5 * π / 3)
    (hC : signedArea2 (capU3 δ) (pt 0 0) (pt 1 0) < 0) :
    0 < δ ∧ δ < π / 3 := by
  have hc32 : Real.cos (3 * π / 2) = 0 := by
    rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring, Real.cos_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hs32 : Real.sin (3 * π / 2) = -1 := by
    rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring, Real.sin_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hsc : Real.cos (δ - π / 6) = -Real.sin (4 * π / 3 + δ) := by
    rw [show δ - π / 6 = (4 * π / 3 + δ) - 3 * π / 2 by ring, Real.cos_sub, hc32, hs32]; ring
  have hCeq : signedArea2 (capU3 δ) (pt 0 0) (pt 1 0)
      = Real.sqrt 3 / 2 - Real.cos (δ - π / 6) := by
    rw [hsc]
    simp only [signedArea2, capU3, pt, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hCeq] at hC
  have hcosgt : Real.cos (π / 6) < Real.cos (δ - π / 6) := by rw [Real.cos_pi_div_six]; linarith
  have h0 : (0 : ℝ) ≤ π / 6 := by positivity
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    have hnp : δ - π / 6 ≤ 0 := by linarith
    have hge : π / 6 ≤ |δ - π / 6| := by rw [abs_of_nonpos hnp]; linarith
    have hle : |δ - π / 6| ≤ π := by rw [abs_of_nonpos hnp]; linarith [Real.pi_pos]
    have := Real.cos_le_cos_of_nonneg_of_le_pi h0 hle hge
    rw [Real.cos_abs] at this
    linarith
  · by_contra h
    push_neg at h
    have hp_ge : π / 6 ≤ δ - π / 6 := by linarith
    by_cases hpi : δ - π / 6 ≤ π
    · have := Real.cos_le_cos_of_nonneg_of_le_pi h0 hpi hp_ge
      linarith
    · push_neg at hpi
      have h1 : π / 2 ≤ δ - π / 6 := by linarith [Real.pi_pos]
      have h2 : δ - π / 6 ≤ π + π / 2 := by linarith
      have hnp := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
      have hp6 : (0 : ℝ) < Real.cos (π / 6) := by rw [Real.cos_pi_div_six]; positivity
      linarith
theorem normSim_chainImage_capU3 (p₁ p₂ p₃ w : ℝ²) (hp : p₁ ≠ p₂)
    (h31 : dist p₁ p₂ = dist p₃ p₁) (h23 : dist p₁ p₂ = dist p₂ p₃)
    (hori : 0 < signedArea2 p₁ p₂ p₃)
    (hw3 : dist w p₃ = dist p₁ p₂)
    (hchord : signedArea2 w p₁ p₂ < 0) :
    ∃ δ : ℝ, normSim p₁ p₂ w = capU3 δ ∧ 0 < δ ∧ δ < π / 3 := by
  have hLpos : 0 < (p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2 := b3n9m082_normSim_ℓ2_pos hp
  have h3img : normSim p₁ p₂ p₃ = pt (1 / 2) (Real.sqrt 3 / 2) :=
    normSim_thd p₁ p₂ p₃ hp h31 h23 hori
  have hone : dist (normSim p₁ p₂ w) (pt (1 / 2) (Real.sqrt 3 / 2)) = 1 := by
    rw [← h3img, normSim_dist_image p₁ p₂ hp w p₃, hw3, inv_mul_cancel₀ (dist_ne_zero.mpr hp)]
  obtain ⟨δ, hδlo, hδhi, hδeq⟩ := exists_capU3_of_dist_v3_one _ hone
  have hC : signedArea2 (capU3 δ) (pt 0 0) (pt 1 0) < 0 := by
    have ht := signedArea2_normSim p₁ p₂ hp w p₁ p₂
    rw [hδeq, normSim_fst p₁ p₂, normSim_snd p₁ p₂ hp] at ht
    rw [ht]; exact mul_neg_of_pos_of_neg (inv_pos.mpr hLpos) hchord
  obtain ⟨hδ0, hδ1⟩ := capU3_arg_range δ hδlo hδhi hC
  exact ⟨δ, hδeq, hδ0, hδ1⟩
theorem n8a3_normSimChain_capU2 (p₁ p₂ p₃ s : ℝ²) (hp : p₁ ≠ p₂)
    (h31 : dist p₁ p₂ = dist p₃ p₁) (h23 : dist p₁ p₂ = dist p₂ p₃)
    (hori : 0 < signedArea2 p₁ p₂ p₃)
    (hs1 : dist s p₁ = dist p₁ p₂) (hschord : signedArea2 s p₂ p₃ < 0)
    {m : ℕ} (L : FiniteEndpoint.OrderedSideChain m) (γ : Fin m → ℝ)
    (hγmem : ∀ i, γ i ∈ Set.Icc (0 : ℝ) (π / 3)) (hγmono : StrictMono γ)
    (hL : ∀ i, normSim p₁ p₂ (L.points i) = capU2 (γ i)) :
    N8a3AdjacentCapDistanceStrict s L := by
  obtain ⟨α, hsα, hα0, hα1⟩ := normSim_centre_image p₁ p₂ p₃ s hp h31 h23 hori hs1 hschord
  exact n8a3_of_distScalingToCapU2 (inv_pos.mpr (dist_pos.mpr hp))
    (normSim_dist_image p₁ p₂ hp) L hα0 hα1 γ hγmem hγmono hsα hL
theorem n8a3_normSimChain_capU3 (p₁ p₂ p₃ s : ℝ²) (hp : p₁ ≠ p₂)
    (h31 : dist p₁ p₂ = dist p₃ p₁) (h23 : dist p₁ p₂ = dist p₂ p₃)
    (hori : 0 < signedArea2 p₁ p₂ p₃)
    (hs1 : dist s p₁ = dist p₁ p₂) (hschord : signedArea2 s p₂ p₃ < 0)
    {m : ℕ} (L : FiniteEndpoint.OrderedSideChain m) (δ : Fin m → ℝ)
    (hδmem : ∀ i, δ i ∈ Set.Icc (0 : ℝ) (π / 3)) (hδanti : StrictAnti δ)
    (hL : ∀ i, normSim p₁ p₂ (L.points i) = capU3 (δ i)) :
    N8a3AdjacentCapDistanceStrict s L := by
  obtain ⟨α, hsα, hα0, hα1⟩ := normSim_centre_image p₁ p₂ p₃ s hp h31 h23 hori hs1 hschord
  exact n8a3_of_distScalingToCapU3 (inv_pos.mpr (dist_pos.mpr hp))
    (normSim_dist_image p₁ p₂ hp) L hα0 hα1 δ hδmem hδanti hsα hL
theorem signedArea2_capU2_eq_sin (a b : ℝ) :
    signedArea2 (pt 1 0) (capU2 a) (capU2 b) = Real.sin (b - a) := by
  simp only [signedArea2, capU2, pt, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show b - a = (2 * π / 3 + b) - (2 * π / 3 + a) by ring, Real.sin_sub]
  ring
theorem signedArea2_capU3_eq_sin (a b : ℝ) :
    signedArea2 (pt (1 / 2) (Real.sqrt 3 / 2)) (capU3 a) (capU3 b) = Real.sin (b - a) := by
  simp only [signedArea2, capU3, pt, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show b - a = (4 * π / 3 + b) - (4 * π / 3 + a) by ring, Real.sin_sub]
  ring
theorem b3n9m082_sin_nonpos_of_nonpos_of_neg_pi_le {x : ℝ} (hge : -π ≤ x) (hle : x ≤ 0) :
    Real.sin x ≤ 0 := by
  rw [show x = -(-x) by ring, Real.sin_neg]
  have : 0 ≤ Real.sin (-x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  linarith
theorem normSim_capU2_strictMono_of_orient (p₁ p₂ : ℝ²) (hp : p₁ ≠ p₂)
    {m : ℕ} (L : FiniteEndpoint.OrderedSideChain m) (γ : Fin m → ℝ)
    (hγmem : ∀ i, γ i ∈ Set.Icc (0 : ℝ) (π / 3))
    (hL : ∀ i, normSim p₁ p₂ (L.points i) = capU2 (γ i))
    (horient : ∀ i j, i < j → 0 < signedArea2 p₂ (L.points i) (L.points j)) :
    StrictMono γ := by
  intro i j hij
  have hconst : 0 < ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2)⁻¹ :=
    inv_pos.mpr (b3n9m082_normSim_ℓ2_pos hp)
  have hpos : 0 < signedArea2 (normSim p₁ p₂ p₂) (normSim p₁ p₂ (L.points i))
      (normSim p₁ p₂ (L.points j)) := by
    rw [signedArea2_normSim p₁ p₂ hp p₂ (L.points i) (L.points j)]
    exact mul_pos hconst (horient i j hij)
  rw [normSim_snd p₁ p₂ hp, hL i, hL j, signedArea2_capU2_eq_sin] at hpos
  by_contra hcon
  push_neg at hcon
  have hle : γ i - γ j ≤ π := by
    have := (hγmem i).2; have := (hγmem j).1; linarith [Real.pi_pos]
  have hsin : Real.sin (γ j - γ i) ≤ 0 :=
    b3n9m082_sin_nonpos_of_nonpos_of_neg_pi_le (x := γ j - γ i) (by linarith) (by linarith)
  linarith
theorem normSim_capU3_strictAnti_of_orient (p₁ p₂ p₃ : ℝ²) (hp : p₁ ≠ p₂)
    (h31 : dist p₁ p₂ = dist p₃ p₁) (h23 : dist p₁ p₂ = dist p₂ p₃)
    (hori : 0 < signedArea2 p₁ p₂ p₃)
    {m : ℕ} (L : FiniteEndpoint.OrderedSideChain m) (δ : Fin m → ℝ)
    (hδmem : ∀ i, δ i ∈ Set.Icc (0 : ℝ) (π / 3))
    (hL : ∀ i, normSim p₁ p₂ (L.points i) = capU3 (δ i))
    (horient : ∀ i j, i < j → signedArea2 p₃ (L.points i) (L.points j) < 0) :
    StrictAnti δ := by
  intro i j hij
  have hconst : 0 < ((p₂ 0 - p₁ 0) ^ 2 + (p₂ 1 - p₁ 1) ^ 2)⁻¹ :=
    inv_pos.mpr (b3n9m082_normSim_ℓ2_pos hp)
  have hneg : signedArea2 (normSim p₁ p₂ p₃) (normSim p₁ p₂ (L.points i))
      (normSim p₁ p₂ (L.points j)) < 0 := by
    rw [signedArea2_normSim p₁ p₂ hp p₃ (L.points i) (L.points j)]
    exact mul_neg_of_pos_of_neg hconst (horient i j hij)
  rw [normSim_thd p₁ p₂ p₃ hp h31 h23 hori, hL i, hL j, signedArea2_capU3_eq_sin] at hneg
  by_contra hcon
  push_neg at hcon
  have hge : 0 ≤ δ j - δ i := by linarith
  have hle : δ j - δ i ≤ π := by
    have := (hδmem j).2; have := (hδmem i).1; linarith [Real.pi_pos]
  have : 0 ≤ Real.sin (δ j - δ i) := Real.sin_nonneg_of_nonneg_of_le_pi hge hle
  linarith
theorem n8a3_normSimChain_capU2_oriented (p₁ p₂ p₃ s : ℝ²) (hp : p₁ ≠ p₂)
    (h31 : dist p₁ p₂ = dist p₃ p₁) (h23 : dist p₁ p₂ = dist p₂ p₃)
    (hori : 0 < signedArea2 p₁ p₂ p₃)
    (hs1 : dist s p₁ = dist p₁ p₂) (hschord : signedArea2 s p₂ p₃ < 0)
    {m : ℕ} (L : FiniteEndpoint.OrderedSideChain m) (γ : Fin m → ℝ)
    (hγmem : ∀ i, γ i ∈ Set.Icc (0 : ℝ) (π / 3))
    (hL : ∀ i, normSim p₁ p₂ (L.points i) = capU2 (γ i))
    (horient : ∀ i j, i < j → 0 < signedArea2 p₂ (L.points i) (L.points j)) :
    N8a3AdjacentCapDistanceStrict s L :=
  n8a3_normSimChain_capU2 p₁ p₂ p₃ s hp h31 h23 hori hs1 hschord L γ hγmem
    (normSim_capU2_strictMono_of_orient p₁ p₂ hp L γ hγmem hL horient) hL
theorem n8a3_normSimChain_capU3_oriented (p₁ p₂ p₃ s : ℝ²) (hp : p₁ ≠ p₂)
    (h31 : dist p₁ p₂ = dist p₃ p₁) (h23 : dist p₁ p₂ = dist p₂ p₃)
    (hori : 0 < signedArea2 p₁ p₂ p₃)
    (hs1 : dist s p₁ = dist p₁ p₂) (hschord : signedArea2 s p₂ p₃ < 0)
    {m : ℕ} (L : FiniteEndpoint.OrderedSideChain m) (δ : Fin m → ℝ)
    (hδmem : ∀ i, δ i ∈ Set.Icc (0 : ℝ) (π / 3))
    (hL : ∀ i, normSim p₁ p₂ (L.points i) = capU3 (δ i))
    (horient : ∀ i j, i < j → signedArea2 p₃ (L.points i) (L.points j) < 0) :
    N8a3AdjacentCapDistanceStrict s L :=
  n8a3_normSimChain_capU3 p₁ p₂ p₃ s hp h31 h23 hori hs1 hschord L δ hδmem
    (normSim_capU3_strictAnti_of_orient p₁ p₂ p₃ hp h31 h23 hori L δ hδmem hL horient) hL
end Problem97
end Batch3N9
end Batch3N9Unit082

-- Original module: Solutions.Batch3N9.N8.N8CapCoordNorm
section Batch3N9Unit083
namespace Batch3N9
open Real Set
open scoped EuclideanGeometry
open scoped RealInnerProductSpace
open EuclideanGeometry
open Finset
namespace Problem97
theorem signedArea2_swap23 (a b c : ℝ²) :
    signedArea2 a b c = - signedArea2 a c b := by
  simp only [signedArea2]; ring
theorem onArcOpposite_swap (vi vj vk v : ℝ²) :
    OnArcOpposite vi vj vk v ↔ OnArcOpposite vi vk vj v := by
  unfold OnArcOpposite
  rw [signedArea2_swap23 v vk vj, signedArea2_swap23 vi vk vj]
  constructor <;> intro h <;> nlinarith only [h]
theorem signedArea2_ne_zero_of_equilateral
    {v₁ v₂ v₃ : ℝ²} {d : ℝ} (hd : 0 < d)
    (e12 : dist v₁ v₂ = d) (e13 : dist v₁ v₃ = d) (e23 : dist v₂ v₃ = d)
    (hp12 : v₁ ≠ v₂) (hp23 : v₂ ≠ v₃) (hp13 : v₁ ≠ v₃) :
    signedArea2 v₁ v₂ v₃ ≠ 0 := by
  intro hz
  have hcol : Collinear ℝ ({v₁, v₂, v₃} : Set ℝ²) :=
    collinear_of_signedArea2_eq_zero v₁ v₂ v₃ hz
  have e21 : dist v₂ v₁ = d := by rw [dist_comm]; exact e12
  have e31 : dist v₃ v₁ = d := by rw [dist_comm]; exact e13
  have e32 : dist v₃ v₂ = d := by rw [dist_comm]; exact e23
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · have hs : Sbtw ℝ v₁ v₂ v₃ := ⟨hw, hp12.symm, hp23⟩
    have hd' := hs.dist_lt_max_dist v₁
    rw [dist_self, e21, e31, max_eq_right hd.le] at hd'; exact lt_irrefl d hd'
  · have hs : Sbtw ℝ v₂ v₃ v₁ := ⟨hw, hp23.symm, hp13.symm⟩
    have hd' := hs.dist_lt_max_dist v₂
    rw [dist_self, e32, e12, max_eq_right hd.le] at hd'; exact lt_irrefl d hd'
  · have hs : Sbtw ℝ v₃ v₁ v₂ := ⟨hw, hp13, hp12⟩
    have hd' := hs.dist_lt_max_dist v₃
    rw [dist_self, e13, e23, max_eq_right hd.le] at hd'; exact lt_irrefl d hd'
theorem exists_apex_frame
    {v₁ v₂ v₃ x : ℝ²} {d : ℝ} (hd : 0 < d)
    (hp12 : v₁ ≠ v₂) (hp23 : v₂ ≠ v₃) (hp13 : v₁ ≠ v₃)
    (e12 : dist v₁ v₂ = d) (e13 : dist v₁ v₃ = d) (e23 : dist v₂ v₃ = d)
    (hx1 : dist v₁ x = d)
    (harc : OnArcOpposite v₁ v₂ v₃ x)
    (hxv2 : x ≠ v₂) (hxv3 : x ≠ v₃) :
    ∃ a₂ a₃ : ℝ²,
      v₁ ≠ a₂ ∧
      dist v₁ a₂ = dist a₃ v₁ ∧ dist v₁ a₂ = dist a₂ a₃ ∧
      0 < signedArea2 v₁ a₂ a₃ ∧
      dist x v₁ = dist v₁ a₂ ∧
      signedArea2 x a₂ a₃ < 0 := by
  have hxv1 : dist x v₁ = d := by rw [dist_comm]; exact hx1
  have e21 : dist v₂ v₁ = d := by rw [dist_comm]; exact e12
  have e31 : dist v₃ v₁ = d := by rw [dist_comm]; exact e13
  have e32 : dist v₃ v₂ = d := by rw [dist_comm]; exact e23
  have hxchord_ne : signedArea2 x v₂ v₃ ≠ 0 :=
    Problem97.MEC.signedArea2_ne_zero_of_three_dist_eq hxv1 e21 e31 hxv2 hp23 hxv3
  have htri_ne : signedArea2 v₁ v₂ v₃ ≠ 0 :=
    signedArea2_ne_zero_of_equilateral hd e12 e13 e23 hp12 hp23 hp13
  have harc' : signedArea2 x v₂ v₃ * signedArea2 v₁ v₂ v₃ ≤ 0 := harc
  rcases lt_or_gt_of_ne htri_ne with hneg | hpos
  ·
    have hpos_swap : 0 < signedArea2 v₁ v₃ v₂ := by
      rw [signedArea2_swap23 v₁ v₃ v₂]; linarith
    have hxpos : 0 < signedArea2 x v₂ v₃ := by
      rcases lt_or_gt_of_ne hxchord_ne with hc | hc
      · exfalso; nlinarith only [harc', hneg, hc]
      · exact hc
    refine ⟨v₃, v₂, hp13, ?_, ?_, hpos_swap, ?_, ?_⟩
    · rw [e13, e21]
    · rw [e13, e32]
    · rw [hxv1, e13]
    · rw [signedArea2_swap23 x v₃ v₂]; linarith
  ·
    have hxneg : signedArea2 x v₂ v₃ < 0 := by
      rcases lt_or_gt_of_ne hxchord_ne with hc | hc
      · exact hc
      · exfalso; nlinarith only [harc', hpos, hc]
    refine ⟨v₂, v₃, hp12, ?_, ?_, hpos, ?_, hxneg⟩
    · rw [e12, e31]
    · rw [e12, e23]
    · rw [hxv1, e12]
noncomputable def twoPointChain (w₁ w₂ : ℝ²) (hne : w₁ ≠ w₂) :
    FiniteEndpoint.OrderedSideChain 2 where
  points := ![w₁, w₂]
  injective := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
theorem twoPointChain_support (w₁ w₂ : ℝ²) (hne : w₁ ≠ w₂) :
    (twoPointChain w₁ w₂ hne).support = ({w₁, w₂} : Finset ℝ²) := by
  ext z
  simp only [FiniteEndpoint.OrderedSideChain.mem_support_iff, twoPointChain, Finset.mem_insert,
    Finset.mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
theorem n8a3_twoPoint_capU2pos {v₁ v₂ v₃ x w₁ w₂ : ℝ²} {d : ℝ} (hne : w₁ ≠ w₂)
    (hp12 : v₁ ≠ v₂)
    (e12 : dist v₁ v₂ = d) (e13 : dist v₁ v₃ = d) (e23 : dist v₂ v₃ = d)
    (hpos : 0 < signedArea2 v₁ v₂ v₃)
    (hx1 : dist v₁ x = d) (hxchord : signedArea2 x v₂ v₃ < 0)
    (hw1d : dist w₁ v₂ = d) (hw2d : dist w₂ v₂ = d)
    (hw1chord : signedArea2 w₁ v₃ v₁ < 0) (hw2chord : signedArea2 w₂ v₃ v₁ < 0)
    (horient01 : 0 < signedArea2 v₂ w₁ w₂) :
    N8a3AdjacentCapDistanceStrict x (twoPointChain w₁ w₂ hne) := by
  have h31 : dist v₁ v₂ = dist v₃ v₁ := by rw [e12, dist_comm, e13]
  have h23 : dist v₁ v₂ = dist v₂ v₃ := by rw [e12, e23]
  obtain ⟨γ₁, hγ1eq, hγ10, hγ11⟩ :=
    normSim_chainImage_capU2 v₁ v₂ v₃ w₁ hp12 h31 h23 hpos (by rw [hw1d, e12]) hw1chord
  obtain ⟨γ₂, hγ2eq, hγ20, hγ21⟩ :=
    normSim_chainImage_capU2 v₁ v₂ v₃ w₂ hp12 h31 h23 hpos (by rw [hw2d, e12]) hw2chord
  apply n8a3_normSimChain_capU2_oriented v₁ v₂ v₃ x hp12 h31 h23 hpos
    (by rw [dist_comm, hx1, e12]) hxchord (twoPointChain w₁ w₂ hne) ![γ₁, γ₂]
  · intro i; fin_cases i
    · exact ⟨hγ10.le, hγ11.le⟩
    · exact ⟨hγ20.le, hγ21.le⟩
  · intro i; fin_cases i
    · exact hγ1eq
    · exact hγ2eq
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [twoPointChain]
theorem n8a3_twoPoint_capU3neg {v₁ v₂ v₃ x w₁ w₂ : ℝ²} {d : ℝ} (hne : w₁ ≠ w₂)
    (hp13 : v₁ ≠ v₃)
    (e12 : dist v₁ v₂ = d) (e13 : dist v₁ v₃ = d) (e23 : dist v₂ v₃ = d)
    (hneg : signedArea2 v₁ v₂ v₃ < 0)
    (hx1 : dist v₁ x = d) (hxchord3 : signedArea2 x v₃ v₂ < 0)
    (hw1d : dist w₁ v₂ = d) (hw2d : dist w₂ v₂ = d)
    (hw1chord3 : signedArea2 w₁ v₁ v₃ < 0) (hw2chord3 : signedArea2 w₂ v₁ v₃ < 0)
    (horient01 : signedArea2 v₂ w₁ w₂ < 0) :
    N8a3AdjacentCapDistanceStrict x (twoPointChain w₁ w₂ hne) := by
  have hposF : 0 < signedArea2 v₁ v₃ v₂ := by rw [signedArea2_swap23 v₁ v₃ v₂]; linarith
  have h31 : dist v₁ v₃ = dist v₂ v₁ := by rw [e13, dist_comm, e12]
  have h23 : dist v₁ v₃ = dist v₃ v₂ := by rw [e13, dist_comm, e23]
  obtain ⟨δ₁, hδ1eq, hδ10, hδ11⟩ :=
    normSim_chainImage_capU3 v₁ v₃ v₂ w₁ hp13 h31 h23 hposF (by rw [hw1d, e13]) hw1chord3
  obtain ⟨δ₂, hδ2eq, hδ20, hδ21⟩ :=
    normSim_chainImage_capU3 v₁ v₃ v₂ w₂ hp13 h31 h23 hposF (by rw [hw2d, e13]) hw2chord3
  apply n8a3_normSimChain_capU3_oriented v₁ v₃ v₂ x hp13 h31 h23 hposF
    (by rw [dist_comm, hx1, e13]) hxchord3 (twoPointChain w₁ w₂ hne) ![δ₁, δ₂]
  · intro i; fin_cases i
    · exact ⟨hδ10.le, hδ11.le⟩
    · exact ⟨hδ20.le, hδ21.le⟩
  · intro i; fin_cases i
    · exact hδ1eq
    · exact hδ2eq
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [twoPointChain]
theorem exists_adjacentMonotoneChain {v₁ v₂ v₃ x w₁ w₂ : ℝ²} {d : ℝ}
    (hne : w₁ ≠ w₂) (hp12 : v₁ ≠ v₂) (hp13 : v₁ ≠ v₃)
    (e12 : dist v₁ v₂ = d) (e13 : dist v₁ v₃ = d) (e23 : dist v₂ v₃ = d)
    (htri_ne : signedArea2 v₁ v₂ v₃ ≠ 0)
    (hx1 : dist v₁ x = d) (harcx : OnArcOpposite v₁ v₂ v₃ x)
    (hxchord_ne : signedArea2 x v₂ v₃ ≠ 0)
    (hw1d : dist w₁ v₂ = d) (hw2d : dist w₂ v₂ = d)
    (harcw1 : OnArcOpposite v₂ v₃ v₁ w₁) (harcw2 : OnArcOpposite v₂ v₃ v₁ w₂)
    (hw1cn : signedArea2 w₁ v₃ v₁ ≠ 0) (hw2cn : signedArea2 w₂ v₃ v₁ ≠ 0)
    (horient_ne : signedArea2 v₂ w₁ w₂ ≠ 0) :
    ∃ (chain : FiniteEndpoint.OrderedSideChain 2),
      chain.support = ({w₁, w₂} : Finset ℝ²) ∧ N8a3AdjacentCapDistanceStrict x chain := by
  have hcyc : signedArea2 v₂ v₃ v₁ = signedArea2 v₁ v₂ v₃ := by simp only [signedArea2]; ring
  rcases lt_or_gt_of_ne htri_ne with hneg | hpos
  ·
    have hxchord3 : signedArea2 x v₃ v₂ < 0 := by
      have hprod : signedArea2 x v₂ v₃ * signedArea2 v₁ v₂ v₃ ≤ 0 := harcx
      have hxpos : 0 < signedArea2 x v₂ v₃ := by
        rcases lt_or_gt_of_ne hxchord_ne with hc | hc
        · exfalso; nlinarith only [hprod, hneg, hc]
        · exact hc
      rw [signedArea2_swap23 x v₃ v₂]; linarith
    have hw1c3 : signedArea2 w₁ v₁ v₃ < 0 := by
      have hprod : signedArea2 w₁ v₃ v₁ * signedArea2 v₂ v₃ v₁ ≤ 0 := harcw1
      rw [hcyc] at hprod
      have : 0 < signedArea2 w₁ v₃ v₁ := by
        rcases lt_or_gt_of_ne hw1cn with hc | hc
        · exfalso; nlinarith only [hprod, hneg, hc]
        · exact hc
      rw [signedArea2_swap23 w₁ v₁ v₃]; linarith
    have hw2c3 : signedArea2 w₂ v₁ v₃ < 0 := by
      have hprod : signedArea2 w₂ v₃ v₁ * signedArea2 v₂ v₃ v₁ ≤ 0 := harcw2
      rw [hcyc] at hprod
      have : 0 < signedArea2 w₂ v₃ v₁ := by
        rcases lt_or_gt_of_ne hw2cn with hc | hc
        · exfalso; nlinarith only [hprod, hneg, hc]
        · exact hc
      rw [signedArea2_swap23 w₂ v₁ v₃]; linarith
    rcases lt_or_gt_of_ne horient_ne with hwlt | hwgt
    · exact ⟨twoPointChain w₁ w₂ hne, twoPointChain_support w₁ w₂ hne,
        n8a3_twoPoint_capU3neg hne hp13 e12 e13 e23 hneg hx1 hxchord3 hw1d hw2d hw1c3 hw2c3 hwlt⟩
    · have hswap : signedArea2 v₂ w₂ w₁ < 0 := by
        rw [signedArea2_swap23 v₂ w₂ w₁]; linarith
      refine ⟨twoPointChain w₂ w₁ hne.symm, ?_, ?_⟩
      · rw [twoPointChain_support, Finset.pair_comm]
      · exact @n8a3_twoPoint_capU3neg v₁ v₂ v₃ x w₂ w₁ d hne.symm hp13 e12 e13 e23 hneg
          hx1 hxchord3 hw2d hw1d hw2c3 hw1c3 hswap
  ·
    have hxchord : signedArea2 x v₂ v₃ < 0 := by
      have hprod : signedArea2 x v₂ v₃ * signedArea2 v₁ v₂ v₃ ≤ 0 := harcx
      rcases lt_or_gt_of_ne hxchord_ne with hc | hc
      · exact hc
      · exfalso; nlinarith only [hprod, hpos, hc]
    have hposcyc : 0 < signedArea2 v₂ v₃ v₁ := by rw [hcyc]; exact hpos
    have hw1c : signedArea2 w₁ v₃ v₁ < 0 := by
      have hprod : signedArea2 w₁ v₃ v₁ * signedArea2 v₂ v₃ v₁ ≤ 0 := harcw1
      rcases lt_or_gt_of_ne hw1cn with hc | hc
      · exact hc
      · exfalso; nlinarith only [hprod, hcyc, hc, hpos]
    have hw2c : signedArea2 w₂ v₃ v₁ < 0 := by
      have hprod : signedArea2 w₂ v₃ v₁ * signedArea2 v₂ v₃ v₁ ≤ 0 := harcw2
      rcases lt_or_gt_of_ne hw2cn with hc | hc
      · exact hc
      · exfalso; nlinarith only [hprod, hcyc, hc, hpos]
    rcases lt_or_gt_of_ne horient_ne with hwlt | hwgt
    · have hswap : 0 < signedArea2 v₂ w₂ w₁ := by
        rw [signedArea2_swap23 v₂ w₂ w₁]; linarith
      refine ⟨twoPointChain w₂ w₁ hne.symm, ?_, ?_⟩
      · rw [twoPointChain_support, Finset.pair_comm]
      · exact @n8a3_twoPoint_capU2pos v₁ v₂ v₃ x w₂ w₁ d hne.symm hp12 e12 e13 e23 hpos
          hx1 hxchord hw2d hw1d hw2c hw1c hswap
    · exact ⟨twoPointChain w₁ w₂ hne, twoPointChain_support w₁ w₂ hne,
        n8a3_twoPoint_capU2pos hne hp12 e12 e13 e23 hpos hx1 hxchord hw1d hw2d hw1c hw2c hwgt⟩
theorem build_adjacentArcWitness {v₁ v₂ v₃ x w₁ w₂ : ℝ²} {d r : ℝ}
    (hne : w₁ ≠ w₂) (hp12 : v₁ ≠ v₂) (hp13 : v₁ ≠ v₃)
    (e12 : dist v₁ v₂ = d) (e13 : dist v₁ v₃ = d) (e23 : dist v₂ v₃ = d)
    (htri_ne : signedArea2 v₁ v₂ v₃ ≠ 0)
    (hx1 : dist v₁ x = d) (harcx : OnArcOpposite v₁ v₂ v₃ x)
    (hxv2 : x ≠ v₂)
    (hxchord_ne : signedArea2 x v₂ v₃ ≠ 0)
    (hw1d : dist w₁ v₂ = d) (hw2d : dist w₂ v₂ = d)
    (harcw1 : OnArcOpposite v₂ v₃ v₁ w₁) (harcw2 : OnArcOpposite v₂ v₃ v₁ w₂)
    (hw1cn : signedArea2 w₁ v₃ v₁ ≠ 0) (hw2cn : signedArea2 w₂ v₃ v₁ ≠ 0)
    (horient_ne : signedArea2 v₂ w₁ w₂ ≠ 0)
    (capPts : Finset ℝ²) (hcap : capPts = ({w₁, w₂} : Finset ℝ²))
    (hcapdist : ∀ z ∈ capPts, dist v₂ z = d) :
    ∃ W : N8AdjacentArcWitness,
      W.base.apex = x ∧ W.base.selectedRadius = r ∧ W.base.arc.support = capPts := by
  obtain ⟨chain, hchainsupp, hmono⟩ :=
    exists_adjacentMonotoneChain hne hp12 hp13 e12 e13 e23 htri_ne hx1 harcx hxchord_ne
      hw1d hw2d harcw1 harcw2 hw1cn hw2cn horient_ne
  let arc : N8ArcCircle :=
    { support := capPts, circleCenter := v₂, circleRadius := d, on_circle := hcapdist }
  have hcircles_ne : (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨arc.circleCenter, arc.circleRadius⟩ := by
    intro h; exact hxv2 (congrArg EuclideanGeometry.Sphere.center h)
  have hcovers : arc.support ⊆ chain.support := by
    change capPts ⊆ chain.support; rw [hchainsupp, hcap]
  exact ⟨{ base := { apex := x, selectedRadius := r, arc := arc, circles_ne := hcircles_ne }
           m := 2, chain := chain, chain_covers := hcovers, monotone := hmono }, rfl, rfl, rfl⟩
theorem no_equidistant_apex_at_side
    (a b c x : ℝ²) (D : ℝ) (hD : 0 < D)
    (hab : dist a b = D) (hbc : dist b c = D) (hca : dist c a = D)
    (hxa : dist x a = D) (hxb : dist x b = D) (hxc : dist x c = D) : False := by
  set u := a - x with hu
  set v := b - x with hv
  set w := c - x with hw
  have nu : ‖u‖ = D := by rw [hu, ← dist_eq_norm, dist_comm]; exact hxa
  have nv : ‖v‖ = D := by rw [hv, ← dist_eq_norm, dist_comm]; exact hxb
  have nw : ‖w‖ = D := by rw [hw, ← dist_eq_norm, dist_comm]; exact hxc
  have iuv : ⟪u, v⟫ = D ^ 2 / 2 := by
    have h1 : ‖u - v‖ = D := by
      have huv : u - v = a - b := by rw [hu, hv]; abel
      rw [huv, ← dist_eq_norm]; exact hab
    have e := norm_sub_sq_real u v; rw [h1, nu, nv] at e; nlinarith only [e]
  have ivw : ⟪v, w⟫ = D ^ 2 / 2 := by
    have h1 : ‖v - w‖ = D := by
      have hvw : v - w = b - c := by rw [hv, hw]; abel
      rw [hvw, ← dist_eq_norm]; exact hbc
    have e := norm_sub_sq_real v w; rw [h1, nv, nw] at e; nlinarith only [e]
  have iuw : ⟪u, w⟫ = D ^ 2 / 2 := by
    have h1 : ‖u - w‖ = D := by
      have huw : u - w = a - c := by rw [hu, hw]; abel
      rw [huw, ← dist_eq_norm, dist_comm]; exact hca
    have e := norm_sub_sq_real u w; rw [h1, nu, nw] at e; nlinarith only [e]
  have iuu : ⟪u, u⟫ = D ^ 2 := by rw [real_inner_self_eq_norm_sq, nu]
  have ivv : ⟪v, v⟫ = D ^ 2 := by rw [real_inner_self_eq_norm_sq, nv]
  have iww : ⟪w, w⟫ = D ^ 2 := by rw [real_inner_self_eq_norm_sq, nw]
  have hLI : LinearIndependent ℝ ![u, v, w] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : g 0 • u + g 1 • v + g 2 • w = 0 := by
      have hg' := hg; simp [Fin.sum_univ_three] at hg'
      convert hg' using 2
    have eu : g 0 * ⟪u, u⟫ + g 1 * ⟪u, v⟫ + g 2 * ⟪u, w⟫ = 0 := by
      have h := congrArg (fun z => ⟪u, z⟫) hsum
      simpa only [inner_add_right, inner_smul_right, inner_zero_right] using h
    have ev : g 0 * ⟪v, u⟫ + g 1 * ⟪v, v⟫ + g 2 * ⟪v, w⟫ = 0 := by
      have h := congrArg (fun z => ⟪v, z⟫) hsum
      simpa only [inner_add_right, inner_smul_right, inner_zero_right] using h
    have ew : g 0 * ⟪w, u⟫ + g 1 * ⟪w, v⟫ + g 2 * ⟪w, w⟫ = 0 := by
      have h := congrArg (fun z => ⟪w, z⟫) hsum
      simpa only [inner_add_right, inner_smul_right, inner_zero_right] using h
    rw [real_inner_comm u v, iuv, ivv, ivw] at ev
    rw [real_inner_comm u w, real_inner_comm v w, iuw, ivw, iww] at ew
    rw [iuu, iuv, iuw] at eu
    have hD2 : (0 : ℝ) < D ^ 2 := by positivity
    have hsum : (g 0 + g 1 + g 2) * (2 * D ^ 2) = 0 := by linear_combination eu + ev + ew
    have hs : g 0 + g 1 + g 2 = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact h
      · exfalso; linarith
    have h0 : g 0 * D ^ 2 = 0 := by linear_combination 2 * eu - D ^ 2 * hs
    have h1 : g 1 * D ^ 2 = 0 := by linear_combination 2 * ev - D ^ 2 * hs
    have h2 : g 2 * D ^ 2 = 0 := by linear_combination 2 * ew - D ^ 2 * hs
    intro i; fin_cases i
    · exact (mul_eq_zero.mp h0).resolve_right (by linarith)
    · exact (mul_eq_zero.mp h1).resolve_right (by linarith)
    · exact (mul_eq_zero.mp h2).resolve_right (by linarith)
  have hcard := hLI.fintype_card_le_finrank
  simp [finrank_euclideanSpace] at hcard
namespace FiniteEndpointShell
theorem exists_apexFrameData
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (hN4e : S.N4eCapContainment)
    (i : Fin 3) {x : ℝ²} (hx : x ∈ S.capInteriorByIndex i) :
    ∃ v₁ v₂ v₃ : ℝ²,
      v₁ ≠ v₂ ∧
      dist v₁ v₂ = dist v₃ v₁ ∧ dist v₁ v₂ = dist v₂ v₃ ∧
      0 < signedArea2 v₁ v₂ v₃ ∧
      dist x v₁ = dist v₁ v₂ ∧
      signedArea2 x v₂ v₃ < 0 := by
  classical
  obtain ⟨d, hdpos, hC1, hC2, hC3⟩ := Erdos9796FiniteNine.circle_placement S hN4e
  have hp12 : S.triangle.v1 ≠ S.triangle.v2 := S.triangle.v12_ne
  have hp23 : S.triangle.v2 ≠ S.triangle.v3 := S.triangle.v23_ne
  have hp13 : S.triangle.v1 ≠ S.triangle.v3 := S.triangle.v13_ne
  have e12 : dist S.triangle.v1 S.triangle.v2 = d := hC1 _ S.CP.v2_mem_C1
  have e13 : dist S.triangle.v1 S.triangle.v3 = d := hC1 _ S.CP.v3_mem_C1
  have e23 : dist S.triangle.v2 S.triangle.v3 = d := hC2 _ S.CP.v3_mem_C2
  fin_cases i
  ·
    simp only [capInteriorByIndex] at hx
    unfold FiniteEndpointShell.I1 at hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxv3, hxv2, hxC⟩ := hx
    have hxA : x ∈ A := S.CP.C1_subset hxC
    have harc : OnArcOpposite S.triangle.v1 S.triangle.v2 S.triangle.v3 x :=
      ((S.CP.arc_membership x hxA).1).mp hxC
    have hx1 : dist S.triangle.v1 x = d := hC1 _ hxC
    obtain ⟨a₂, a₃, hne, h31, h23', hori, hxd, hchord⟩ :=
      exists_apex_frame hdpos hp12 hp23 hp13 e12 e13 e23 hx1 harc hxv2 hxv3
    exact ⟨S.triangle.v1, a₂, a₃, hne, h31, h23', hori, hxd, hchord⟩
  ·
    simp only [capInteriorByIndex] at hx
    unfold FiniteEndpointShell.I2 at hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxv1, hxv3, hxC⟩ := hx
    have hxA : x ∈ A := S.CP.C2_subset hxC
    have harc : OnArcOpposite S.triangle.v2 S.triangle.v3 S.triangle.v1 x :=
      ((S.CP.arc_membership x hxA).2.1).mp hxC
    have hx1 : dist S.triangle.v2 x = d := hC2 _ hxC
    obtain ⟨a₂, a₃, hne, h31, h23', hori, hxd, hchord⟩ :=
      exists_apex_frame hdpos hp23 hp13.symm hp12.symm e23
        (by rw [dist_comm]; exact e12) (by rw [dist_comm]; exact e13) hx1 harc hxv3 hxv1
    exact ⟨S.triangle.v2, a₂, a₃, hne, h31, h23', hori, hxd, hchord⟩
  ·
    simp only [capInteriorByIndex] at hx
    unfold FiniteEndpointShell.I3 at hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxv2, hxv1, hxC⟩ := hx
    have hxA : x ∈ A := S.CP.C3_subset hxC
    have harc : OnArcOpposite S.triangle.v3 S.triangle.v1 S.triangle.v2 x :=
      ((S.CP.arc_membership x hxA).2.2).mp hxC
    have hx1 : dist S.triangle.v3 x = d := hC3 _ hxC
    obtain ⟨a₂, a₃, hne, h31, h23', hori, hxd, hchord⟩ :=
      exists_apex_frame hdpos hp13.symm hp12 hp23.symm
        (by rw [dist_comm]; exact e13) (by rw [dist_comm]; exact e23) e12 hx1 harc hxv1 hxv2
    exact ⟨S.triangle.v3, a₂, a₃, hne, h31, h23', hori, hxd, hchord⟩
theorem build_shell_adjacentArcWitness {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {va vb vc x : ℝ²} {d r : ℝ} (hdpos : 0 < d)
    (hab : va ≠ vb) (hac : va ≠ vc) (hbc : vb ≠ vc)
    (haA : va ∈ A) (hbA : vb ∈ A) (hcA : vc ∈ A)
    (eab : dist va vb = d) (eac : dist va vc = d) (ebc : dist vb vc = d)
    (hxA : x ∈ A) (hxb : x ≠ vb) (hxc : x ≠ vc)
    (harcx : OnArcOpposite va vb vc x) (hx1 : dist va x = d)
    (Iadj : Finset ℝ²) (hadjcard : Iadj.card = 2) (hadjsub : Iadj ⊆ A)
    (hunpack : ∀ w ∈ Iadj, w ≠ vc ∧ w ≠ va ∧ OnArcOpposite vb vc va w ∧ dist vb w = d) :
    ∃ W : N8AdjacentArcWitness,
      W.base.apex = x ∧ W.base.selectedRadius = r ∧ W.base.arc.support = Iadj := by
  classical
  have htri_ne : signedArea2 va vb vc ≠ 0 :=
    signedArea2_ne_zero_of_equilateral hdpos eab eac ebc hab hbc hac
  have hncoll : ∀ {a b c : ℝ²}, a ∈ A → b ∈ A → c ∈ A → a ≠ b → a ≠ c → b ≠ c →
      signedArea2 a b c ≠ 0 := by
    intro a b c ha hb hc hab' hac' hbc' hz
    exact ConvexIndep.not_three_collinear S.hconv ha hb hc hab' hac' hbc'
      (collinear_of_signedArea2_eq_zero a b c hz)
  have hxchord_ne : signedArea2 x vb vc ≠ 0 := hncoll hxA hbA hcA hxb hxc hbc
  obtain ⟨w₁, w₂, hw12ne, hIeq⟩ := Finset.card_eq_two.mp hadjcard
  have hw1mem : w₁ ∈ Iadj := by rw [hIeq]; simp
  have hw2mem : w₂ ∈ Iadj := by rw [hIeq]; simp
  obtain ⟨hw1c, hw1a, harcw1, hw1d⟩ := hunpack w₁ hw1mem
  obtain ⟨hw2c, hw2a, harcw2, hw2d⟩ := hunpack w₂ hw2mem
  have hw1A : w₁ ∈ A := hadjsub hw1mem
  have hw2A : w₂ ∈ A := hadjsub hw2mem
  have hw1cn : signedArea2 w₁ vc va ≠ 0 := hncoll hw1A hcA haA hw1c hw1a hac.symm
  have hw2cn : signedArea2 w₂ vc va ≠ 0 := hncoll hw2A hcA haA hw2c hw2a hac.symm
  have hv_b_w1 : vb ≠ w₁ := by intro h; rw [← h, dist_self] at hw1d; linarith
  have hv_b_w2 : vb ≠ w₂ := by intro h; rw [← h, dist_self] at hw2d; linarith
  have horient_ne : signedArea2 vb w₁ w₂ ≠ 0 := hncoll hbA hw1A hw2A hv_b_w1 hv_b_w2 hw12ne
  refine build_adjacentArcWitness (r := r) hw12ne hab hac eab eac ebc htri_ne hx1 harcx hxb
    hxchord_ne (by rw [dist_comm]; exact hw1d) (by rw [dist_comm]; exact hw2d)
    harcw1 harcw2 hw1cn hw2cn horient_ne Iadj hIeq ?_
  intro z hz
  exact (hunpack z hz).2.2.2
theorem exists_leftAdjacentArcWitness {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) (i : Fin 3) {x : ℝ²} (hx : x ∈ S.capInteriorByIndex i)
    (r : ℝ) :
    ∃ W : N8AdjacentArcWitness,
      W.base.apex = x ∧ W.base.selectedRadius = r ∧
        W.base.arc.support = S.leftAdjacentInteriorByIndex i := by
  classical
  obtain ⟨d, hdpos, hC1, hC2, hC3⟩ := Erdos9796FiniteNine.circle_placement S hN4e
  have hp12 : S.triangle.v1 ≠ S.triangle.v2 := S.triangle.v12_ne
  have hp23 : S.triangle.v2 ≠ S.triangle.v3 := S.triangle.v23_ne
  have hp13 : S.triangle.v1 ≠ S.triangle.v3 := S.triangle.v13_ne
  have e12 : dist S.triangle.v1 S.triangle.v2 = d := hC1 _ S.CP.v2_mem_C1
  have e13 : dist S.triangle.v1 S.triangle.v3 = d := hC1 _ S.CP.v3_mem_C1
  have e23 : dist S.triangle.v2 S.triangle.v3 = d := hC2 _ S.CP.v3_mem_C2
  have hcards := S.n4b_n5_exact_cap_vector_of_interior_lower_bounds
    S.I1_card_ge_two S.I2_card_ge_two S.I3_card_ge_two
  have hv1A := S.triangle.v1_mem
  have hv2A := S.triangle.v2_mem
  have hv3A := S.triangle.v3_mem
  fin_cases i
  ·
    simp only [capInteriorByIndex] at hx
    rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxv3, hxv2, hxC⟩ := hx
    have hxA : x ∈ A := S.CP.C1_subset hxC
    have harcx : OnArcOpposite S.triangle.v1 S.triangle.v2 S.triangle.v3 x :=
      ((S.CP.arc_membership x hxA).1).mp hxC
    have hx1 : dist S.triangle.v1 x = d := hC1 _ hxC
    show ∃ W : N8AdjacentArcWitness, W.base.apex = x ∧ W.base.selectedRadius = r ∧
      W.base.arc.support = S.I2
    refine build_shell_adjacentArcWitness S (r := r) hdpos hp12 hp13 hp23 hv1A hv2A hv3A
      e12 e13 e23 hxA hxv2 hxv3 harcx hx1 S.I2 hcards.2.2.2.2.1 ?_ ?_
    · intro w hw; rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hw
      exact S.CP.C2_subset hw.2.2
    · intro w hw
      rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hw
      obtain ⟨hwv1, hwv3, hwC2⟩ := hw
      exact ⟨hwv3, hwv1, ((S.CP.arc_membership w (S.CP.C2_subset hwC2)).2.1).mp hwC2, hC2 _ hwC2⟩
  ·
    simp only [capInteriorByIndex] at hx
    rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxv1, hxv3, hxC⟩ := hx
    have hxA : x ∈ A := S.CP.C2_subset hxC
    have harcx : OnArcOpposite S.triangle.v2 S.triangle.v3 S.triangle.v1 x :=
      ((S.CP.arc_membership x hxA).2.1).mp hxC
    have hx1 : dist S.triangle.v2 x = d := hC2 _ hxC
    show ∃ W : N8AdjacentArcWitness, W.base.apex = x ∧ W.base.selectedRadius = r ∧
      W.base.arc.support = S.I3
    refine build_shell_adjacentArcWitness S (r := r) hdpos hp23 hp12.symm hp13.symm hv2A hv3A hv1A
      e23 (by rw [dist_comm]; exact e12) (by rw [dist_comm]; exact e13)
      hxA hxv3 hxv1 harcx hx1 S.I3 hcards.2.2.2.2.2 ?_ ?_
    · intro w hw; rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hw
      exact S.CP.C3_subset hw.2.2
    · intro w hw
      rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hw
      obtain ⟨hwv2, hwv1, hwC3⟩ := hw
      exact ⟨hwv1, hwv2, ((S.CP.arc_membership w (S.CP.C3_subset hwC3)).2.2).mp hwC3, hC3 _ hwC3⟩
  ·
    simp only [capInteriorByIndex] at hx
    rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxv2, hxv1, hxC⟩ := hx
    have hxA : x ∈ A := S.CP.C3_subset hxC
    have harcx : OnArcOpposite S.triangle.v3 S.triangle.v1 S.triangle.v2 x :=
      ((S.CP.arc_membership x hxA).2.2).mp hxC
    have hx1 : dist S.triangle.v3 x = d := hC3 _ hxC
    show ∃ W : N8AdjacentArcWitness, W.base.apex = x ∧ W.base.selectedRadius = r ∧
      W.base.arc.support = S.I1
    refine build_shell_adjacentArcWitness S (r := r) hdpos hp13.symm hp23.symm hp12 hv3A hv1A hv2A
      (by rw [dist_comm]; exact e13) (by rw [dist_comm]; exact e23) e12
      hxA hxv1 hxv2 harcx hx1 S.I1 hcards.2.2.2.1 ?_ ?_
    · intro w hw; rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hw
      exact S.CP.C1_subset hw.2.2
    · intro w hw
      rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hw
      obtain ⟨hwv3, hwv2, hwC1⟩ := hw
      exact ⟨hwv2, hwv3, ((S.CP.arc_membership w (S.CP.C1_subset hwC1)).1).mp hwC1, hC1 _ hwC1⟩
theorem exists_rightAdjacentArcWitness {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) (i : Fin 3) {x : ℝ²} (hx : x ∈ S.capInteriorByIndex i)
    (r : ℝ) :
    ∃ W : N8AdjacentArcWitness,
      W.base.apex = x ∧ W.base.selectedRadius = r ∧
        W.base.arc.support = S.rightAdjacentInteriorByIndex i := by
  classical
  obtain ⟨d, hdpos, hC1, hC2, hC3⟩ := Erdos9796FiniteNine.circle_placement S hN4e
  have hp12 : S.triangle.v1 ≠ S.triangle.v2 := S.triangle.v12_ne
  have hp23 : S.triangle.v2 ≠ S.triangle.v3 := S.triangle.v23_ne
  have hp13 : S.triangle.v1 ≠ S.triangle.v3 := S.triangle.v13_ne
  have e12 : dist S.triangle.v1 S.triangle.v2 = d := hC1 _ S.CP.v2_mem_C1
  have e13 : dist S.triangle.v1 S.triangle.v3 = d := hC1 _ S.CP.v3_mem_C1
  have e23 : dist S.triangle.v2 S.triangle.v3 = d := hC2 _ S.CP.v3_mem_C2
  have hcards := S.n4b_n5_exact_cap_vector_of_interior_lower_bounds
    S.I1_card_ge_two S.I2_card_ge_two S.I3_card_ge_two
  have hv1A := S.triangle.v1_mem
  have hv2A := S.triangle.v2_mem
  have hv3A := S.triangle.v3_mem
  fin_cases i
  ·
    simp only [capInteriorByIndex] at hx
    rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxv3, hxv2, hxC⟩ := hx
    have hxA : x ∈ A := S.CP.C1_subset hxC
    have harcx : OnArcOpposite S.triangle.v1 S.triangle.v3 S.triangle.v2 x :=
      (onArcOpposite_swap _ _ _ _).mp (((S.CP.arc_membership x hxA).1).mp hxC)
    have hx1 : dist S.triangle.v1 x = d := hC1 _ hxC
    show ∃ W : N8AdjacentArcWitness, W.base.apex = x ∧ W.base.selectedRadius = r ∧
      W.base.arc.support = S.I3
    refine build_shell_adjacentArcWitness S (r := r) hdpos hp13 hp12 hp23.symm hv1A hv3A hv2A
      e13 e12 (by rw [dist_comm]; exact e23) hxA hxv3 hxv2 harcx hx1 S.I3 hcards.2.2.2.2.2 ?_ ?_
    · intro w hw; rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hw
      exact S.CP.C3_subset hw.2.2
    · intro w hw
      rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hw
      obtain ⟨hwv2, hwv1, hwC3⟩ := hw
      exact ⟨hwv2, hwv1,
        (onArcOpposite_swap _ _ _ _).mp
          (((S.CP.arc_membership w (S.CP.C3_subset hwC3)).2.2).mp hwC3),
        hC3 _ hwC3⟩
  ·
    simp only [capInteriorByIndex] at hx
    rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxv1, hxv3, hxC⟩ := hx
    have hxA : x ∈ A := S.CP.C2_subset hxC
    have harcx : OnArcOpposite S.triangle.v2 S.triangle.v1 S.triangle.v3 x :=
      (onArcOpposite_swap _ _ _ _).mp (((S.CP.arc_membership x hxA).2.1).mp hxC)
    have hx1 : dist S.triangle.v2 x = d := hC2 _ hxC
    show ∃ W : N8AdjacentArcWitness, W.base.apex = x ∧ W.base.selectedRadius = r ∧
      W.base.arc.support = S.I1
    refine build_shell_adjacentArcWitness S (r := r) hdpos hp12.symm hp23 hp13 hv2A hv1A hv3A
      (by rw [dist_comm]; exact e12) e23 e13
      hxA hxv1 hxv3 harcx hx1 S.I1 hcards.2.2.2.1 ?_ ?_
    · intro w hw; rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hw
      exact S.CP.C1_subset hw.2.2
    · intro w hw
      rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hw
      obtain ⟨hwv3, hwv2, hwC1⟩ := hw
      exact ⟨hwv3, hwv2,
        (onArcOpposite_swap _ _ _ _).mp
          (((S.CP.arc_membership w (S.CP.C1_subset hwC1)).1).mp hwC1),
        hC1 _ hwC1⟩
  ·
    simp only [capInteriorByIndex] at hx
    rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxv2, hxv1, hxC⟩ := hx
    have hxA : x ∈ A := S.CP.C3_subset hxC
    have harcx : OnArcOpposite S.triangle.v3 S.triangle.v2 S.triangle.v1 x :=
      (onArcOpposite_swap _ _ _ _).mp (((S.CP.arc_membership x hxA).2.2).mp hxC)
    have hx1 : dist S.triangle.v3 x = d := hC3 _ hxC
    show ∃ W : N8AdjacentArcWitness, W.base.apex = x ∧ W.base.selectedRadius = r ∧
      W.base.arc.support = S.I2
    refine build_shell_adjacentArcWitness S (r := r) hdpos hp23.symm hp13.symm hp12.symm hv3A hv2A hv1A
      (by rw [dist_comm]; exact e23) (by rw [dist_comm]; exact e13) (by rw [dist_comm]; exact e12)
      hxA hxv2 hxv1 harcx hx1 S.I2 hcards.2.2.2.2.1 ?_ ?_
    · intro w hw; rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hw
      exact S.CP.C2_subset hw.2.2
    · intro w hw
      rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hw
      obtain ⟨hwv1, hwv3, hwC2⟩ := hw
      exact ⟨hwv1, hwv3,
        (onArcOpposite_swap _ _ _ _).mp
          (((S.CP.arc_membership w (S.CP.C2_subset hwC2)).2.1).mp hwC2),
        hC2 _ hwC2⟩
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit083

-- Original module: Solutions.Batch3N9.N8.N8kDistribution
section Batch3N9Unit084
namespace Batch3N9
open scoped EuclideanGeometry
open scoped InnerProductSpace
open EuclideanGeometry
open Finset
namespace Problem97
lemma b3n9m084_angular_prop_dist (x v2 v3 o : ℝ²)
    (hdist_xv2v3 : dist x v2 = dist x v3)
    (hdist_v2v3o : dist v2 v3 = dist v2 o)
    (hdist_xo : dist x o = dist x v3)
    (hsa : signedArea2 o x v2 = -signedArea2 x v2 v3) :
    dist x v2 ^ 2 * signedArea2 o v2 v3 = dist v2 v3 ^ 2 * signedArea2 x v2 v3 := by
  have dist_sq : ∀ p q : ℝ², dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 :=
    Problem97.dist_sq_coord
  have h1 : (x 0 - v2 0) ^ 2 + (x 1 - v2 1) ^ 2 =
            (x 0 - v3 0) ^ 2 + (x 1 - v3 1) ^ 2 := by
    have := dist_sq x v2 ▸ dist_sq x v3 ▸ (congr_arg (· ^ 2) hdist_xv2v3); linarith
  have h2 : (v2 0 - v3 0) ^ 2 + (v2 1 - v3 1) ^ 2 =
            (v2 0 - o 0) ^ 2 + (v2 1 - o 1) ^ 2 := by
    have := dist_sq v2 v3 ▸ dist_sq v2 o ▸ (congr_arg (· ^ 2) hdist_v2v3o); linarith
  have h3 : (x 0 - o 0) ^ 2 + (x 1 - o 1) ^ 2 =
            (x 0 - v3 0) ^ 2 + (x 1 - v3 1) ^ 2 := by
    have := dist_sq x o ▸ dist_sq x v3 ▸ (congr_arg (· ^ 2) hdist_xo); linarith
  simp only [signedArea2] at *
  rw [dist_sq x v2, dist_sq v2 v3]
  linear_combination
    ((v2 0 - o 0) * (x 1 - o 1) - (v2 1 - o 1) * (x 0 - o 0)) * h1 +
    (-(v2 0 - o 0) * (v3 1 - o 1) + 3/2 * (v2 0 - o 0) * (x 1 - o 1) +
     (v2 1 - o 1) * (v3 0 - o 0) - 3/2 * (v2 1 - o 1) * (x 0 - o 0) -
     (v3 0 - o 0) * (x 1 - o 1) + (v3 1 - o 1) * (x 0 - o 0)) * h2 +
    (-1/2 * (v2 0 - o 0) * (x 1 - o 1) + 1/2 * (v2 1 - o 1) * (x 0 - o 0)) * h3 +
    (-(v2 0 - o 0) * (x 0 - o 0) - (v2 1 - o 1) * (x 1 - o 1)) * hsa
set_option maxRecDepth 4000 in
lemma b3n9m084_rc_refl_closed (x a e : ℝ²) :
    EuclideanGeometry.reflection (affineSpan ℝ ({x, a} : Set ℝ²)) e =
      ((2:ℝ) • ((Submodule.span ℝ ({x - a} : Set ℝ²)).starProjection (e - x)) - (e - x)) + x := by
  have hx_mem : x ∈ affineSpan ℝ ({x, a} : Set ℝ²) := left_mem_affineSpan_pair ..
  have hdir : (affineSpan ℝ ({x, a} : Set ℝ²)).direction
      = Submodule.span ℝ ({x - a} : Set ℝ²) := by
    rw [direction_affineSpan, vectorSpan_pair]; rfl
  rw [EuclideanGeometry.reflection_apply_of_mem _ e hx_mem, Submodule.reflection_apply]
  simp only [hdir, vsub_eq_sub, vadd_eq_add]; module
set_option maxRecDepth 4000 in
lemma b3n9m084_rc_o_coord (x a e : ℝ²) (i : Fin 2) :
    (EuclideanGeometry.reflection (affineSpan ℝ ({x, a} : Set ℝ²)) e) i
      = (2:ℝ) * ((inner ℝ (x - a) (e - x)) / (‖x - a‖^2)) * ((x - a) i)
        - (e - x) i + x i := by
  rw [b3n9m084_rc_refl_closed, Submodule.starProjection_singleton]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    RCLike.ofReal_real_eq_id, id_eq]
  ring
lemma b3n9m084_rc_inner_coord (u v : ℝ²) : (inner ℝ u v) = u 0 * v 0 + u 1 * v 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two, mul_comm]
lemma b3n9m084_rc_nsq_coord (u : ℝ²) : ‖u‖^2 = (u 0)^2 + (u 1)^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]
set_option maxRecDepth 4000 in
lemma b3n9m084_signedArea2_reflection_chord (x c e w : ℝ²) :
    signedArea2 (EuclideanGeometry.reflection (affineSpan ℝ ({x, c} : Set ℝ²)) e) e w
      * dist x c ^ 2
      = 2 * signedArea2 x c e * ⟪c - x, e - w⟫_ℝ := by
  rcases eq_or_ne x c with rfl | hxc
  · simp [signedArea2, dist_self, sub_self, inner_zero_left, mul_zero]
  · rw [dist_eq_norm]
    have hden : (x 0 - c 0)^2 + (x 1 - c 1)^2 ≠ 0 := by
      intro hz; apply hxc
      have h0 : x 0 - c 0 = 0 := by nlinarith only [hz, sq_nonneg (x 0 - c 0), sq_nonneg (x 1 - c 1)]
      have h1 : x 1 - c 1 = 0 := by nlinarith only [hz, sq_nonneg (x 0 - c 0), sq_nonneg (x 1 - c 1)]
      ext j; fin_cases j <;> simp_all <;> linarith
    have e0 : (x - c) 0 = x 0 - c 0 := by simp
    have e1 : (x - c) 1 = x 1 - c 1 := by simp
    have e2 : (e - x) 0 = e 0 - x 0 := by simp
    have e3 : (e - x) 1 = e 1 - x 1 := by simp
    have e4 : (c - x) 0 = c 0 - x 0 := by simp
    have e5 : (c - x) 1 = c 1 - x 1 := by simp
    have e6 : (e - w) 0 = e 0 - w 0 := by simp
    have e7 : (e - w) 1 = e 1 - w 1 := by simp
    unfold signedArea2
    rw [show (EuclideanGeometry.reflection (affineSpan ℝ ({x, c} : Set ℝ²)) e) 0 = _
          from b3n9m084_rc_o_coord x c e 0,
        show (EuclideanGeometry.reflection (affineSpan ℝ ({x, c} : Set ℝ²)) e) 1 = _
          from b3n9m084_rc_o_coord x c e 1,
        b3n9m084_rc_inner_coord (x - c) (e - x), b3n9m084_rc_inner_coord (c - x) (e - w), b3n9m084_rc_nsq_coord (x - c),
        e0, e1, e2, e3, e4, e5, e6, e7]
    field_simp
    ring
lemma b3n9m084_dist_apex_chord_endpoint_lt
    {va vb vc x : ℝ²} {d : ℝ} (hd : 0 < d)
    (hxa : dist va x = d) (eab : dist va vb = d) (eac : dist va vc = d) (ebc : dist vb vc = d)
    (hbc : vb ≠ vc) (hxc : x ≠ vc)
    (harc : signedArea2 x vb vc * signedArea2 va vb vc ≤ 0) :
    dist x vb < d := by
  have nrm : ∀ p q : ℝ², ‖p - q‖ = dist p q := fun p q => by rw [dist_eq_norm]
  have hxan : ‖x - va‖ ^ 2 = ‖vb - va‖ ^ 2 := by
    rw [nrm, nrm, dist_comm x va, hxa, dist_comm vb va, eab]
  have hbcn : ‖vb - va‖ ^ 2 = ‖vc - va‖ ^ 2 := by
    rw [nrm, nrm, dist_comm vb va, eab, dist_comm vc va, eac]
  have hoff := inner_chord_eq_two_mul_inner_midpoint_off_sphere vb vc x va hbcn
  have hbr := inner_midpoint_eq_signedArea_prod_of_chord_sphere vb vc x va hbcn
  have hSqpos : 0 < ‖vc - vb‖ ^ 2 := by
    have : vc - vb ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc); positivity
  have hrhs : signedArea2 va vb vc * signedArea2 x vb vc ≤ 0 := by rw [mul_comm]; exact harc
  have hinner_le : ⟪midpoint ℝ vb vc - x, midpoint ℝ vb vc - va⟫_ℝ ≤ 0 := by
    have hh : ⟪midpoint ℝ vb vc - x, midpoint ℝ vb vc - va⟫_ℝ * ‖vc - vb‖ ^ 2 ≤ 0 := by
      rw [hbr]; exact hrhs
    exact nonpos_of_mul_nonpos_left hh hSqpos
  have hcomm : ⟪midpoint ℝ vb vc - va, midpoint ℝ vb vc - x⟫_ℝ
      = ⟪midpoint ℝ vb vc - x, midpoint ℝ vb vc - va⟫_ℝ := real_inner_comm _ _
  have hcorr : ‖x - va‖ ^ 2 - ‖vb - va‖ ^ 2 = 0 := by rw [hxan]; ring
  have hthales : ⟪vb - x, vc - x⟫_ℝ ≤ 0 := by rw [hoff, hcomm]; linarith [hinner_le, hcorr]
  have hexp : ‖vb - vc‖ ^ 2 = ‖vb - x‖ ^ 2 + ‖vc - x‖ ^ 2 - 2 * ⟪vb - x, vc - x⟫_ℝ := by
    have h : vb - vc = (vb - x) - (vc - x) := by abel
    rw [h, @norm_sub_sq_real]; ring
  have hvcx_pos : 0 < ‖vc - x‖ ^ 2 := by
    have : vc - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxc); positivity
  have hdbc : ‖vb - vc‖ = d := by rw [nrm]; exact ebc
  have hlt : ‖vb - x‖ ^ 2 < d ^ 2 := by rw [← hdbc, hexp]; nlinarith only [hxan, hoff, hinner_le, hcomm, hvcx_pos, hthales]
  have hdist : dist x vb = ‖vb - x‖ := by rw [dist_eq_norm, norm_sub_rev]
  rw [hdist]
  nlinarith only [hd, hlt, norm_nonneg (vb - x), sq_nonneg (‖vb - x‖ - d), sq_nonneg (‖vb - x‖ + d)]
lemma b3n9m084_sameSide_prod_pos_apexVertex
    {va vb vc x : ℝ²} {d : ℝ} (hd : 0 < d)
    (hxa : dist va x = d) (eab : dist va vb = d) (eac : dist va vc = d) (ebc : dist vb vc = d)
    (hab : va ≠ vb)
    (hxc_lt : dist x vc < d) :
    0 < signedArea2 x vb va * signedArea2 vb va vc := by
  have ds : ∀ p q : ℝ², dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 :=
    Problem97.dist_sq_coord
  have hmid : ∀ i : Fin 2, (midpoint ℝ vb va) i = ((vb i + va i) / 2 : ℝ) := by
    intro i; rw [midpoint_eq_smul_add]; simp [PiLp.smul_apply, PiLp.add_apply, invOf_eq_inv]; ring
  have hIexp : ⟪midpoint ℝ vb va - x, midpoint ℝ vb va - vc⟫_ℝ
      = ((vb 0 + va 0) / 2 - x 0) * ((vb 0 + va 0) / 2 - vc 0)
        + ((vb 1 + va 1) / 2 - x 1) * ((vb 1 + va 1) / 2 - vc 1) := by
    rw [@PiLp.inner_apply]; simp only [Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      PiLp.sub_apply, hmid]; ring
  have hxc_lt' : dist x vc ^ 2 < d ^ 2 := by
    have h0 : 0 ≤ dist x vc := dist_nonneg
    nlinarith only [hd, hxc_lt, h0]
  have hI : 0 < ⟪midpoint ℝ vb va - x, midpoint ℝ vb va - vc⟫_ℝ := by
    rw [hIexp]
    have h2 := ds va vb; have h3 := ds va vc; have h4 := ds vb vc
    rw [eab] at h2; rw [eac] at h3; rw [ebc] at h4
    have hgx : (x 0 - va 0) ^ 2 + (x 1 - va 1) ^ 2 = d ^ 2 := by rw [← ds x va, dist_comm, hxa]
    have hL3'' : 0 < ((x 0 - va 0) ^ 2 + (x 1 - va 1) ^ 2) - ((x 0 - vc 0) ^ 2 + (x 1 - vc 1) ^ 2) := by
      rw [hgx, ← ds x vc]; linarith [hxc_lt']
    nlinarith only [h2, h3, h4, hgx, hL3'', hd, sq_nonneg (x 0 - vc 0), sq_nonneg (x 1 - vc 1), sq_nonneg (x 0 - vb 0), sq_nonneg (x 1 - vb 1)]

  have heq : ‖vb - vc‖ = ‖va - vc‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, show dist vb vc = d from ebc,
        show dist va vc = d from eac]
  have hlib := signedArea_prod_pos_of_inner_midpoint_pos heq hab hI
  have hcyc : signedArea2 vc vb va = signedArea2 vb va vc := by simp only [signedArea2]; ring
  rw [hcyc] at hlib; exact hlib
lemma b3n9m084_reflected_chord_prod_pos
    {x c e w : ℝ²} (hxc : x ≠ c)
    (hT : 0 < signedArea2 x c e * ⟪c - x, e - w⟫_ℝ * signedArea2 c e w) :
    0 < signedArea2 (EuclideanGeometry.reflection (affineSpan ℝ ({x, c} : Set ℝ²)) e) e w
          * signedArea2 c e w := by
  have hdxc2 : 0 < dist x c ^ 2 := by have := dist_pos.mpr hxc; positivity
  have hbridge := b3n9m084_signedArea2_reflection_chord x c e w
  have hprod : signedArea2 (EuclideanGeometry.reflection (affineSpan ℝ ({x, c} : Set ℝ²)) e) e w
        * signedArea2 c e w * dist x c ^ 2
      = 2 * (signedArea2 x c e * ⟪c - x, e - w⟫_ℝ * signedArea2 c e w) := by
    linear_combination signedArea2 c e w * hbridge
  nlinarith only [hT, hprod, hdxc2]
lemma b3n9m084_inner_chord_eq_dist_diff (x c e w : ℝ²) :
    2 * ⟪c - x, e - w⟫_ℝ
      = (dist c w ^ 2 - dist c e ^ 2) + (dist x e ^ 2 - dist x w ^ 2) := by
  have ds : ∀ p q : ℝ², dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 :=
    Problem97.dist_sq_coord
  have hInner : ⟪c - x, e - w⟫_ℝ
      = (c 0 - x 0) * (e 0 - w 0) + (c 1 - x 1) * (e 1 - w 1) := by
    rw [@PiLp.inner_apply]; simp [Fin.sum_univ_two, RCLike.inner_apply, mul_comm]
  rw [hInner, ds c w, ds c e, ds x e, ds x w]; ring
lemma b3n9m084_m1_adjacent_empty
    {A : Finset ℝ²} {x c e o : ℝ²} {r d : ℝ}
    {Iadj : Finset ℝ²}
    (hcircles_ne : (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨c, d⟩)
    (heo : e ≠ o)
    (hex : dist x e = r) (heC : dist c e = d)
    (hox : dist x o = r) (hoC : dist c o = d)
    (hIcirc : ∀ z ∈ Iadj, dist c z = d)
    (heI : e ∉ Iadj) (hoI : o ∉ Iadj) :
    (SelectedClass A x r ∩ Iadj).card = 0 := by
  classical
  by_contra hcard0
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard0)
  have hwsel : w ∈ SelectedClass A x r := Finset.mem_of_mem_inter_left hw
  have hwI : w ∈ Iadj := Finset.mem_of_mem_inter_right hw
  have hwx : dist w x = r := dist_self_of_mem_selectedClass hwsel
  have hwC : dist c w = d := hIcirc w hwI
  set s₁ : Sphere ℝ² := ⟨x, r⟩ with hs1
  set s₂ : Sphere ℝ² := ⟨c, d⟩ with hs2
  have hes1 : e ∈ s₁ := EuclideanGeometry.mem_sphere.mpr (by rw [dist_comm]; exact hex)
  have hos1 : o ∈ s₁ := EuclideanGeometry.mem_sphere.mpr (by rw [dist_comm]; exact hox)
  have hes2 : e ∈ s₂ := EuclideanGeometry.mem_sphere.mpr (by rw [dist_comm]; exact heC)
  have hos2 : o ∈ s₂ := EuclideanGeometry.mem_sphere.mpr (by rw [dist_comm]; exact hoC)
  have hws1 : w ∈ s₁ := EuclideanGeometry.mem_sphere.mpr hwx
  have hws2 : w ∈ s₂ := EuclideanGeometry.mem_sphere.mpr (by rw [dist_comm]; exact hwC)
  rcases two_circle_common_point_eq_endpoint hcircles_ne heo hes1 hos1 hes2 hos2 hws1 hws2 with h | h
  · rw [h] at hwI; exact heI hwI
  · rw [h] at hwI; exact hoI hwI
lemma b3n9m084_m1_kill_targeted
    {A : Finset ℝ²} {x c e w : ℝ²} {r d : ℝ} {Iadj : Finset ℝ²}
    (hxc : x ≠ c)
    (hcircles_ne : (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨c, d⟩)
    (hxe : dist x e = r) (hce : dist c e = d)
    (hIcirc : ∀ z ∈ Iadj, dist c z = d)
    (heI : e ∉ Iadj)
    (hcap : ∀ z ∈ Iadj, signedArea2 z e w * signedArea2 c e w ≤ 0)
    (hT : 0 < signedArea2 x c e * ⟪c - x, e - w⟫_ℝ * signedArea2 c e w)
    (hline : e ∉ affineSpan ℝ ({x, c} : Set ℝ²)) :
    (SelectedClass A x r ∩ Iadj).card = 0 := by
  classical
  set sline : AffineSubspace ℝ ℝ² := affineSpan ℝ ({x, c} : Set ℝ²) with hsline
  have hxs : x ∈ sline := by rw [hsline]; exact subset_affineSpan _ _ (by simp)
  have hcs : c ∈ sline := by rw [hsline]; exact subset_affineSpan _ _ (by simp)
  haveI : Nonempty sline := ⟨⟨x, hxs⟩⟩
  set o := EuclideanGeometry.reflection sline e with ho
  have hox : dist x o = r := (EuclideanGeometry.dist_reflection_eq_of_mem sline hxs e).trans hxe
  have hoC : dist c o = d := (EuclideanGeometry.dist_reflection_eq_of_mem sline hcs e).trans hce
  have heo : e ≠ o := by
    intro h
    have hself : EuclideanGeometry.reflection sline e = e := h.symm
    rw [EuclideanGeometry.reflection_eq_self_iff] at hself
    exact hline hself
  have hcapside : 0 < signedArea2 o e w * signedArea2 c e w :=
    b3n9m084_reflected_chord_prod_pos hxc hT
  have hoI : o ∉ Iadj := by
    intro hmem
    have := hcap o hmem
    linarith [hcapside, this]
  exact b3n9m084_m1_adjacent_empty hcircles_ne heo hxe hce hox hoC hIcirc heI hoI
namespace FiniteEndpointShell
noncomputable def moserCount
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (x : ℝ²) (radius : ℝ) : ℕ :=
  (SelectedClass A x radius ∩ S.triangle.verts).card
noncomputable def sameCapCount
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) (x : ℝ²) (radius : ℝ) : ℕ :=
  (SelectedClass A x radius ∩ (S.capInteriorByIndex i).erase x).card
noncomputable def leftAdjCount
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) (x : ℝ²) (radius : ℝ) : ℕ :=
  (SelectedClass A x radius ∩ S.leftAdjacentInteriorByIndex i).card
noncomputable def rightAdjCount
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) (x : ℝ²) (radius : ℝ) : ℕ :=
  (SelectedClass A x radius ∩ S.rightAdjacentInteriorByIndex i).card
theorem apexFrame_moserCount_le_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (hN4e : S.N4eCapContainment)
    (i : Fin 3) {x : ℝ²} (hx : x ∈ S.capInteriorByIndex i) (r : ℝ) :
    S.moserCount x r ≤ 2 := by
  classical
  obtain ⟨d, hdpos, hC1, hC2, hC3⟩ := Erdos9796FiniteNine.circle_placement S hN4e
  have e12 : dist S.triangle.v1 S.triangle.v2 = d := hC1 _ S.CP.v2_mem_C1
  have e13 : dist S.triangle.v1 S.triangle.v3 = d := hC1 _ S.CP.v3_mem_C1
  have e23 : dist S.triangle.v2 S.triangle.v3 = d := hC2 _ S.CP.v3_mem_C2
  have e31 : dist S.triangle.v3 S.triangle.v1 = d := by rw [dist_comm]; exact e13
  by_contra hgt
  push_neg at hgt
  have hm3 : S.moserCount x r = 3 := by
    have hle : S.moserCount x r ≤ 3 := by
      simp only [moserCount]
      calc (SelectedClass A x r ∩ S.triangle.verts).card
          ≤ S.triangle.verts.card := Finset.card_le_card Finset.inter_subset_right
        _ = 3 := S.triangle.verts_card
    omega
  have hsub : S.triangle.verts ⊆ SelectedClass A x r := by
    have hinter : (SelectedClass A x r ∩ S.triangle.verts) = S.triangle.verts := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      rw [S.triangle.verts_card]; rw [← hm3]; rfl
    intro y hy
    have hmem : y ∈ SelectedClass A x r ∩ S.triangle.verts := by rw [hinter]; exact hy
    exact Finset.mem_of_mem_inter_left hmem
  have hv1 : S.triangle.v1 ∈ S.triangle.verts := by simp [MoserTriangle.verts]
  have hv2 : S.triangle.v2 ∈ S.triangle.verts := by simp [MoserTriangle.verts]
  have hv3 : S.triangle.v3 ∈ S.triangle.verts := by simp [MoserTriangle.verts]
  have dx1 : dist x S.triangle.v1 = r := (mem_selectedClass.mp (hsub hv1)).2
  have dx2 : dist x S.triangle.v2 = r := (mem_selectedClass.mp (hsub hv2)).2
  have dx3 : dist x S.triangle.v3 = r := (mem_selectedClass.mp (hsub hv3)).2
  have hrd : r = d := by
    fin_cases i
    · simp only [capInteriorByIndex] at hx
      rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hx
      have hd1 : dist S.triangle.v1 x = d := hC1 _ hx.2.2
      rw [← dx1, dist_comm]; exact hd1
    · simp only [capInteriorByIndex] at hx
      rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hx
      have hd2 : dist S.triangle.v2 x = d := hC2 _ hx.2.2
      rw [← dx2, dist_comm]; exact hd2
    · simp only [capInteriorByIndex] at hx
      rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hx
      have hd3 : dist S.triangle.v3 x = d := hC3 _ hx.2.2
      rw [← dx3, dist_comm]; exact hd3
  subst hrd
  exact no_equidistant_apex_at_side S.triangle.v1 S.triangle.v2 S.triangle.v3 x r hdpos
    e12 e23 e31 dx1 dx2 dx3
theorem selected_le_groupSum
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {x : ℝ²} (i : Fin 3) (radius : ℝ) (hradius_pos : 0 < radius) :
    (SelectedClass A x radius).card ≤
      S.moserCount x radius + S.sameCapCount i x radius +
        S.leftAdjCount i x radius + S.rightAdjCount i x radius := by
  classical
  have hx_notin : x ∉ SelectedClass A x radius := by
    intro hh
    have : dist x x = radius := (mem_selectedClass.mp hh).2
    rw [dist_self] at this; linarith
  have hchain : ∀ (P Q R T : Finset ℝ²),
      SelectedClass A x radius ⊆ P ∪ Q ∪ R ∪ T →
      (SelectedClass A x radius).card ≤ P.card + Q.card + R.card + T.card := by
    intro P Q R T hsub
    calc (SelectedClass A x radius).card
        ≤ (P ∪ Q ∪ R ∪ T).card := Finset.card_le_card hsub
      _ ≤ P.card + Q.card + R.card + T.card := by
          refine le_trans (Finset.card_union_le _ _) ?_
          refine add_le_add (le_trans (Finset.card_union_le _ _) ?_) le_rfl
          exact add_le_add (Finset.card_union_le _ _) le_rfl
  have hqfacts : ∀ q ∈ SelectedClass A x radius, q ∉ S.triangle.verts →
      (q ∈ S.I1 ∨ q ∈ S.I2 ∨ q ∈ S.I3) := by
    intro q hq hqv
    have hqA : q ∈ A := (mem_selectedClass.mp hq).1
    have hone := S.CP.nonmoser_in_one q hqA hqv
    have hqnv : q ≠ S.triangle.v1 ∧ q ≠ S.triangle.v2 ∧ q ≠ S.triangle.v3 := by
      simp only [MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton] at hqv
      push_neg at hqv; exact hqv
    by_cases h1 : q ∈ S.CP.C1
    · refine Or.inl ?_
      rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase]
      exact ⟨hqnv.2.2, hqnv.2.1, h1⟩
    · by_cases h2 : q ∈ S.CP.C2
      · refine Or.inr (Or.inl ?_)
        rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase]
        exact ⟨hqnv.1, hqnv.2.2, h2⟩
      · have h3 : q ∈ S.CP.C3 := by
          by_contra h3; simp only [if_neg h1, if_neg h2, if_neg h3] at hone; omega
        refine Or.inr (Or.inr ?_)
        rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase]
        exact ⟨hqnv.2.1, hqnv.1, h3⟩
  change (SelectedClass A x radius).card ≤
      (SelectedClass A x radius ∩ S.triangle.verts).card +
        (SelectedClass A x radius ∩ (S.capInteriorByIndex i).erase x).card +
        (SelectedClass A x radius ∩ S.leftAdjacentInteriorByIndex i).card +
        (SelectedClass A x radius ∩ S.rightAdjacentInteriorByIndex i).card
  fin_cases i <;>
  · apply hchain
    intro q hq
    have hqx : q ≠ x := fun h => hx_notin (h ▸ hq)
    by_cases hqv : q ∈ S.triangle.verts
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hq, hqv⟩)))
    · rcases hqfacts q hq hqv with hI | hI | hI <;>
      simp only [capInteriorByIndex, leftAdjacentInteriorByIndex,
        rightAdjacentInteriorByIndex] <;>
      first
      | (refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
         exact Finset.mem_inter.mpr ⟨hq, Finset.mem_erase.mpr ⟨hqx, hI⟩⟩)
      | (refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
         exact Finset.mem_inter.mpr ⟨hq, hI⟩)
      | (refine Finset.mem_union_right _ ?_
         exact Finset.mem_inter.mpr ⟨hq, hI⟩)
theorem capInterior_card_eq_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) :
    (S.capInteriorByIndex i).card = 2 := by
  have hc := S.n4b_n5_exact_cap_vector_of_interior_lower_bounds
    S.I1_card_ge_two S.I2_card_ge_two S.I3_card_ge_two
  fin_cases i <;> simp only [FiniteEndpointShell.capInteriorByIndex] <;> simp_all
theorem sameCapCount_le_one
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) {x : ℝ²} (radius : ℝ)
    (hxcap : x ∈ S.capInteriorByIndex i) :
    S.sameCapCount i x radius ≤ 1 := by
  have herase : ((S.capInteriorByIndex i).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hxcap, S.capInterior_card_eq_two]
  calc S.sameCapCount i x radius
      ≤ ((S.capInteriorByIndex i).erase x).card :=
        Finset.card_le_card Finset.inter_subset_right
    _ = 1 := herase
lemma b3n9m084_m1_kill_RI {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {va vb vc x : ℝ²} {d r : ℝ} {Iadj : Finset ℝ²} (hdpos : 0 < d)
    (eab : dist va vb = d) (eac : dist va vc = d) (ebc : dist vb vc = d)
    (hab : va ≠ vb) (hac : va ≠ vc) (hbc : vb ≠ vc)
    (haA : va ∈ A) (hbA : vb ∈ A) (hcA : vc ∈ A)
    (hxA : x ∈ A) (hxa : dist va x = d)
    (hxb : x ≠ vb) (hxc : x ≠ vc)
    (hvm_sel : dist x vc = r)
    (hapex_arc : signedArea2 x vb vc * signedArea2 va vb vc ≤ 0)
    (hIcirc : ∀ z ∈ Iadj, dist vb z = d)
    (hvc_notin : vc ∉ Iadj)
    (hIcap : ∀ z ∈ Iadj, signedArea2 z vc va * signedArea2 vb vc va ≤ 0) :
    (SelectedClass A x r ∩ Iadj).card = 0 := by
  have hcircles_ne : (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨vb, d⟩ := fun h => hxb (congrArg Sphere.center h)
  have hcyc : signedArea2 vb vc va = signedArea2 va vb vc := by simp only [signedArea2]; ring
  have hAne : signedArea2 x vb vc ≠ 0 := by
    have := (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) hxA hbA hcA hxb hxc hbc
    exact fun h => this (collinear_of_signedArea2_eq_zero _ _ _ h)
  have hC'ne : signedArea2 vb vc va ≠ 0 := by
    rw [hcyc]; exact signedArea2_ne_zero_of_equilateral hdpos eab eac ebc hab hbc hac
  have hAC_lt : signedArea2 x vb vc * signedArea2 vb vc va < 0 := by
    rw [hcyc]; exact lt_of_le_of_ne hapex_arc (mul_ne_zero hAne (hcyc ▸ hC'ne))
  have hswap : signedArea2 x vc vb * signedArea2 va vc vb ≤ 0 := by
    have h1 : signedArea2 x vc vb = - signedArea2 x vb vc := by simp only [signedArea2]; ring
    have h2 : signedArea2 va vc vb = - signedArea2 va vb vc := by simp only [signedArea2]; ring
    rw [h1, h2]; nlinarith only [hapex_arc]
  have hstrict : dist x vc < d :=
    b3n9m084_dist_apex_chord_endpoint_lt hdpos hxa eac eab (by rw [dist_comm]; exact ebc) hbc.symm hxb hswap
  have hB : ⟪vb - x, vc - va⟫_ℝ < 0 := by
    have h2b := b3n9m084_inner_chord_eq_dist_diff x vb vc va
    rw [show dist vb va = d by rw [dist_comm]; exact eab, show dist vb vc = d from ebc, hvm_sel,
        show dist x va = d by rw [dist_comm]; exact hxa] at h2b
    have hrd : r < d := by rw [← hvm_sel]; exact hstrict
    nlinarith only [h2b, hdpos, hvm_sel, hstrict, hrd, dist_nonneg (x := x) (y := vc)]
  have hT : 0 < signedArea2 x vb vc * ⟪vb - x, vc - va⟫_ℝ * signedArea2 vb vc va := by
    have h := mul_pos_of_neg_of_neg hAC_lt hB; nlinarith only [h]
  have hline : vc ∉ affineSpan ℝ ({x, vb} : Set ℝ²) := fun hmem =>
    (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) hcA hxA hbA hxc.symm hbc.symm hxb
      (collinear_insert_of_mem_affineSpan_pair hmem)
  exact b3n9m084_m1_kill_targeted hxb hcircles_ne hvm_sel ebc hIcirc hvc_notin hIcap hT hline
lemma b3n9m084_m1_kill_RII {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {va vb vc x : ℝ²} {d r : ℝ} {Iadj : Finset ℝ²} (hdpos : 0 < d)
    (eab : dist va vb = d) (eac : dist va vc = d) (ebc : dist vb vc = d)
    (hab : va ≠ vb) (hac : va ≠ vc) (hbc : vb ≠ vc)
    (haA : va ∈ A) (hbA : vb ∈ A) (hcA : vc ∈ A)
    (hxA : x ∈ A) (hxa : dist va x = d)
    (hxb : x ≠ vb) (hxc : x ≠ vc)
    (hvm_sel : dist x va = r)
    (hapex_arc : signedArea2 x vb vc * signedArea2 va vb vc ≤ 0)
    (hIcirc : ∀ z ∈ Iadj, dist vb z = d)
    (hva_notin : va ∉ Iadj)
    (hIcap : ∀ z ∈ Iadj, signedArea2 z va vc * signedArea2 vb va vc ≤ 0) :
    (SelectedClass A x r ∩ Iadj).card = 0 := by
  have hcircles_ne : (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨vb, d⟩ := fun h => hxb (congrArg Sphere.center h)
  have hce : dist vb va = d := by rw [dist_comm]; exact eab
  have hxa_ne : va ≠ x := fun h => by rw [← h, dist_self] at hxa; linarith
  have hstrict : dist x vc < d := by
    have hswap : signedArea2 x vc vb * signedArea2 va vc vb ≤ 0 := by
      have h1 : signedArea2 x vc vb = - signedArea2 x vb vc := by simp only [signedArea2]; ring
      have h2 : signedArea2 va vc vb = - signedArea2 va vb vc := by simp only [signedArea2]; ring
      rw [h1, h2]; nlinarith only [hapex_arc]
    exact b3n9m084_dist_apex_chord_endpoint_lt hdpos hxa eac eab (by rw [dist_comm]; exact ebc) hbc.symm hxb hswap
  have hAC_pos : 0 < signedArea2 x vb va * signedArea2 vb va vc :=
    b3n9m084_sameSide_prod_pos_apexVertex hdpos hxa eab eac ebc hab hstrict
  have hB : 0 < ⟪vb - x, va - vc⟫_ℝ := by
    have h2b := b3n9m084_inner_chord_eq_dist_diff x vb va vc
    rw [show dist vb vc = d from ebc, show dist vb va = d by rw [dist_comm]; exact eab,
        show dist x va = d by rw [dist_comm]; exact hxa] at h2b
    have hxc_lt' : dist x vc ^ 2 < d ^ 2 := by nlinarith only [hdpos, hstrict, dist_nonneg (x := x) (y := vc)]
    nlinarith only [h2b, hxc_lt']
  have hT : 0 < signedArea2 x vb va * ⟪vb - x, va - vc⟫_ℝ * signedArea2 vb va vc := by
    have h := mul_pos hAC_pos hB; nlinarith only [h]
  have hline : va ∉ affineSpan ℝ ({x, vb} : Set ℝ²) := fun hmem =>
    (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) haA hxA hbA hxa_ne hab hxb
      (collinear_insert_of_mem_affineSpan_pair hmem)
  exact b3n9m084_m1_kill_targeted hxb hcircles_ne hvm_sel hce hIcirc hva_notin hIcap hT hline
lemma b3n9m084_m1_branch_false {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment) {x : ℝ²} {i : Fin 3} {r : ℝ}
    (hx_cap : x ∈ S.capInteriorByIndex i) (hr_pos : 0 < r)
    (hmc : (SelectedClass A x r ∩ S.triangle.verts).card = 1)
    (hl1ge : 1 ≤ (SelectedClass A x r ∩ S.leftAdjacentInteriorByIndex i).card)
    (hr1ge : 1 ≤ (SelectedClass A x r ∩ S.rightAdjacentInteriorByIndex i).card) : False := by
  classical
  obtain ⟨vm, hvm_eq⟩ := Finset.card_eq_one.mp hmc
  have hvm_mem : vm ∈ SelectedClass A x r ∩ S.triangle.verts := by
    rw [hvm_eq]; exact Finset.mem_singleton_self vm
  have hvm_sel : dist x vm = r := (mem_selectedClass.mp (Finset.mem_of_mem_inter_left hvm_mem)).2
  have hvm_verts : vm ∈ S.triangle.verts := Finset.mem_of_mem_inter_right hvm_mem
  obtain ⟨d, hdpos, hC1, hC2, hC3⟩ := Erdos9796FiniteNine.circle_placement S hN4e
  have e12 : dist S.triangle.v1 S.triangle.v2 = d := hC1 _ S.CP.v2_mem_C1
  have e13 : dist S.triangle.v1 S.triangle.v3 = d := hC1 _ S.CP.v3_mem_C1
  have e23 : dist S.triangle.v2 S.triangle.v3 = d := hC2 _ S.CP.v3_mem_C2
  have hp12 : S.triangle.v1 ≠ S.triangle.v2 := S.triangle.v12_ne
  have hp23 : S.triangle.v2 ≠ S.triangle.v3 := S.triangle.v23_ne
  have hp13 : S.triangle.v1 ≠ S.triangle.v3 := S.triangle.v13_ne
  have hv1A := S.triangle.v1_mem
  have hv2A := S.triangle.v2_mem
  have hv3A := S.triangle.v3_mem
  have hI1circ : ∀ z ∈ S.I1, dist S.triangle.v1 z = d := by
    intro z hz; rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hz; exact hC1 z hz.2.2
  have hI2circ : ∀ z ∈ S.I2, dist S.triangle.v2 z = d := by
    intro z hz; rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hz; exact hC2 z hz.2.2
  have hI3circ : ∀ z ∈ S.I3, dist S.triangle.v3 z = d := by
    intro z hz; rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hz; exact hC3 z hz.2.2
  simp only [MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton] at hvm_verts
  have hfinTwo (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one, hfinTwo] at hl1ge hr1ge
  ·
    have hxI1 : x ∈ S.I1 := by have h := hx_cap; simp only [capInteriorByIndex] at h; exact h
    rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hxI1
    obtain ⟨hxv3, hxv2, hxC1⟩ := hxI1
    have hxA : x ∈ A := S.CP.C1_subset hxC1
    have hx1 : dist S.triangle.v1 x = d := hC1 _ hxC1
    have hxarc : signedArea2 x S.triangle.v2 S.triangle.v3 * signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 ≤ 0 :=
      ((S.CP.arc_membership x hxA).1).mp hxC1
    rcases hvm_verts with rfl | rfl | rfl
    ·
      have hkill : (SelectedClass A x r ∩ S.leftAdjacentInteriorByIndex 0).card = 0 := by
        simp only [leftAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
        refine b3n9m084_m1_kill_RII S hdpos e12 e13 e23 hp12 hp13 hp23 hv1A hv2A hv3A hxA
          hx1 hxv2 hxv3 hvm_sel hxarc hI2circ
          (by rw [FiniteEndpointShell.I2]; exact fun h => Finset.notMem_erase _ _ h) ?_
        intro z hz; rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hz
        have harc : signedArea2 z S.triangle.v3 S.triangle.v1 * signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 ≤ 0 :=
          ((S.CP.arc_membership z (S.CP.C2_subset hz.2.2)).2.1).mp hz.2.2
        have h1 : signedArea2 z S.triangle.v1 S.triangle.v3 = -signedArea2 z S.triangle.v3 S.triangle.v1 := by simp only [signedArea2]; ring
        have h2 : signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 = -signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 := by simp only [signedArea2]; ring
        rw [h1, h2]; nlinarith only [harc]
      rw [hkill] at hl1ge; exact absurd hl1ge (by norm_num)
    ·
      have hkill : (SelectedClass A x r ∩ S.rightAdjacentInteriorByIndex 0).card = 0 := by
        simp only [rightAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
        refine b3n9m084_m1_kill_RI S hdpos e13 e12 (by rw [dist_comm]; exact e23) hp13 hp12 hp23.symm
          hv1A hv3A hv2A hxA hx1 hxv3 hxv2 hvm_sel ?_ hI3circ
          (by rw [FiniteEndpointShell.I3]; exact fun h => Finset.notMem_erase _ _ h) ?_
        · have h1 : signedArea2 x S.triangle.v3 S.triangle.v2 = -signedArea2 x S.triangle.v2 S.triangle.v3 := by simp only [signedArea2]; ring
          have h2 : signedArea2 S.triangle.v1 S.triangle.v3 S.triangle.v2 = -signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 := by simp only [signedArea2]; ring
          rw [h1, h2]; nlinarith only [hxarc]
        · intro z hz; rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hz
          have harc : signedArea2 z S.triangle.v1 S.triangle.v2 * signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 ≤ 0 :=
            ((S.CP.arc_membership z (S.CP.C3_subset hz.2.2)).2.2).mp hz.2.2
          have h1 : signedArea2 z S.triangle.v2 S.triangle.v1 = -signedArea2 z S.triangle.v1 S.triangle.v2 := by simp only [signedArea2]; ring
          have h2 : signedArea2 S.triangle.v3 S.triangle.v2 S.triangle.v1 = -signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 := by simp only [signedArea2]; ring
          rw [h1, h2]; nlinarith only [harc]
      rw [hkill] at hr1ge; exact absurd hr1ge (by norm_num)
    ·
      have hkill : (SelectedClass A x r ∩ S.leftAdjacentInteriorByIndex 0).card = 0 := by
        simp only [leftAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
        refine b3n9m084_m1_kill_RI S hdpos e12 e13 e23 hp12 hp13 hp23 hv1A hv2A hv3A hxA
          hx1 hxv2 hxv3 hvm_sel hxarc hI2circ
          (by rw [FiniteEndpointShell.I2]; exact fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)) ?_
        intro z hz; rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hz
        exact ((S.CP.arc_membership z (S.CP.C2_subset hz.2.2)).2.1).mp hz.2.2
      rw [hkill] at hl1ge; exact absurd hl1ge (by norm_num)
  ·
    have hxI2 : x ∈ S.I2 := by have h := hx_cap; simp only [capInteriorByIndex] at h; exact h
    rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hxI2
    obtain ⟨hxv1, hxv3, hxC2⟩ := hxI2
    have hxA : x ∈ A := S.CP.C2_subset hxC2
    have hx2 : dist S.triangle.v2 x = d := hC2 _ hxC2
    have hxarc : signedArea2 x S.triangle.v3 S.triangle.v1 * signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 ≤ 0 :=
      ((S.CP.arc_membership x hxA).2.1).mp hxC2
    rcases hvm_verts with rfl | rfl | rfl
    ·
      have hkill : (SelectedClass A x r ∩ S.leftAdjacentInteriorByIndex 1).card = 0 := by
        simp only [leftAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
        refine b3n9m084_m1_kill_RI S hdpos e23 (by rw [dist_comm]; exact e12) (by rw [dist_comm]; exact e13)
          hp23 hp12.symm hp13.symm hv2A hv3A hv1A hxA hx2 hxv3 hxv1 hvm_sel
          hxarc hI3circ
          (by rw [FiniteEndpointShell.I3]; exact fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)) ?_
        intro z hz; rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hz
        exact ((S.CP.arc_membership z (S.CP.C3_subset hz.2.2)).2.2).mp hz.2.2
      rw [hkill] at hl1ge; exact absurd hl1ge (by norm_num)
    ·
      have hkill : (SelectedClass A x r ∩ S.leftAdjacentInteriorByIndex 1).card = 0 := by
        simp only [leftAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
        refine b3n9m084_m1_kill_RII S hdpos e23 (by rw [dist_comm]; exact e12) (by rw [dist_comm]; exact e13)
          hp23 hp12.symm hp13.symm hv2A hv3A hv1A hxA hx2 hxv3 hxv1 hvm_sel
          hxarc hI3circ
          (by rw [FiniteEndpointShell.I3]; exact fun h => Finset.notMem_erase _ _ h) ?_
        intro z hz; rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hz
        have harc : signedArea2 z S.triangle.v1 S.triangle.v2 * signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 ≤ 0 :=
          ((S.CP.arc_membership z (S.CP.C3_subset hz.2.2)).2.2).mp hz.2.2
        have h1 : signedArea2 z S.triangle.v2 S.triangle.v1 = -signedArea2 z S.triangle.v1 S.triangle.v2 := by simp only [signedArea2]; ring
        have h2 : signedArea2 S.triangle.v3 S.triangle.v2 S.triangle.v1 = -signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 := by simp only [signedArea2]; ring
        rw [h1, h2]; nlinarith only [harc]
      rw [hkill] at hl1ge; exact absurd hl1ge (by norm_num)
    ·
      have hkill : (SelectedClass A x r ∩ S.rightAdjacentInteriorByIndex 1).card = 0 := by
        simp only [rightAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
        refine b3n9m084_m1_kill_RI S hdpos (by rw [dist_comm]; exact e12) e23 e13
          hp12.symm hp23 hp13 hv2A hv1A hv3A hxA hx2 hxv1 hxv3 hvm_sel ?_ hI1circ
          (by rw [FiniteEndpointShell.I1]; exact fun h => Finset.notMem_erase _ _ h) ?_
        · have h1 : signedArea2 x S.triangle.v1 S.triangle.v3 = -signedArea2 x S.triangle.v3 S.triangle.v1 := by simp only [signedArea2]; ring
          have h2 : signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 = -signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 := by simp only [signedArea2]; ring
          rw [h1, h2]; nlinarith only [hxarc]
        · intro z hz; rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hz
          have harc : signedArea2 z S.triangle.v2 S.triangle.v3 * signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 ≤ 0 :=
            ((S.CP.arc_membership z (S.CP.C1_subset hz.2.2)).1).mp hz.2.2
          have h1 : signedArea2 z S.triangle.v3 S.triangle.v2 = -signedArea2 z S.triangle.v2 S.triangle.v3 := by simp only [signedArea2]; ring
          have h2 : signedArea2 S.triangle.v1 S.triangle.v3 S.triangle.v2 = -signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 := by simp only [signedArea2]; ring
          rw [h1, h2]; nlinarith only [harc]
      rw [hkill] at hr1ge; exact absurd hr1ge (by norm_num)
  ·
    have hxI3 : x ∈ S.I3 := by have h := hx_cap; simp only [capInteriorByIndex] at h; exact h
    rw [FiniteEndpointShell.I3, Finset.mem_erase, Finset.mem_erase] at hxI3
    obtain ⟨hxv2, hxv1, hxC3⟩ := hxI3
    have hxA : x ∈ A := S.CP.C3_subset hxC3
    have hx3 : dist S.triangle.v3 x = d := hC3 _ hxC3
    have hxarc : signedArea2 x S.triangle.v1 S.triangle.v2 * signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 ≤ 0 :=
      ((S.CP.arc_membership x hxA).2.2).mp hxC3
    rcases hvm_verts with rfl | rfl | rfl
    ·
      have hkill : (SelectedClass A x r ∩ S.rightAdjacentInteriorByIndex 2).card = 0 := by
        simp only [rightAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
        refine b3n9m084_m1_kill_RI S hdpos (by rw [dist_comm]; exact e23) (by rw [dist_comm]; exact e13) (by rw [dist_comm]; exact e12)
          hp23.symm hp13.symm hp12.symm hv3A hv2A hv1A hxA hx3 hxv2 hxv1 hvm_sel ?_ hI2circ
          (by rw [FiniteEndpointShell.I2]; exact fun h => Finset.notMem_erase _ _ h) ?_
        · have h1 : signedArea2 x S.triangle.v2 S.triangle.v1 = -signedArea2 x S.triangle.v1 S.triangle.v2 := by simp only [signedArea2]; ring
          have h2 : signedArea2 S.triangle.v3 S.triangle.v2 S.triangle.v1 = -signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 := by simp only [signedArea2]; ring
          rw [h1, h2]; nlinarith only [hxarc]
        · intro z hz; rw [FiniteEndpointShell.I2, Finset.mem_erase, Finset.mem_erase] at hz
          have harc : signedArea2 z S.triangle.v3 S.triangle.v1 * signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 ≤ 0 :=
            ((S.CP.arc_membership z (S.CP.C2_subset hz.2.2)).2.1).mp hz.2.2
          have h1 : signedArea2 z S.triangle.v1 S.triangle.v3 = -signedArea2 z S.triangle.v3 S.triangle.v1 := by simp only [signedArea2]; ring
          have h2 : signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 = -signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 := by simp only [signedArea2]; ring
          rw [h1, h2]; nlinarith only [harc]
      rw [hkill] at hr1ge; exact absurd hr1ge (by norm_num)
    ·
      have hkill : (SelectedClass A x r ∩ S.leftAdjacentInteriorByIndex 2).card = 0 := by
        simp only [leftAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
        refine b3n9m084_m1_kill_RI S hdpos (by rw [dist_comm]; exact e13) (by rw [dist_comm]; exact e23) e12
          hp13.symm hp23.symm hp12 hv3A hv1A hv2A hxA hx3 hxv1 hxv2 hvm_sel
          hxarc hI1circ
          (by rw [FiniteEndpointShell.I1]; exact fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)) ?_
        intro z hz; rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hz
        exact ((S.CP.arc_membership z (S.CP.C1_subset hz.2.2)).1).mp hz.2.2
      rw [hkill] at hl1ge; exact absurd hl1ge (by norm_num)
    ·
      have hkill : (SelectedClass A x r ∩ S.leftAdjacentInteriorByIndex 2).card = 0 := by
        simp only [leftAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
        refine b3n9m084_m1_kill_RII S hdpos (by rw [dist_comm]; exact e13) (by rw [dist_comm]; exact e23) e12
          hp13.symm hp23.symm hp12 hv3A hv1A hv2A hxA hx3 hxv1 hxv2 hvm_sel
          hxarc hI1circ
          (by rw [FiniteEndpointShell.I1]; exact fun h => Finset.notMem_erase _ _ h) ?_
        intro z hz; rw [FiniteEndpointShell.I1, Finset.mem_erase, Finset.mem_erase] at hz
        have harc : signedArea2 z S.triangle.v2 S.triangle.v3 * signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 ≤ 0 :=
          ((S.CP.arc_membership z (S.CP.C1_subset hz.2.2)).1).mp hz.2.2
        have h1 : signedArea2 z S.triangle.v3 S.triangle.v2 = -signedArea2 z S.triangle.v2 S.triangle.v3 := by simp only [signedArea2]; ring
        have h2 : signedArea2 S.triangle.v1 S.triangle.v3 S.triangle.v2 = -signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 := by simp only [signedArea2]; ring
        rw [h1, h2]; nlinarith only [harc]
      rw [hkill] at hl1ge; exact absurd hl1ge (by norm_num)
set_option maxHeartbeats 1600000 in
theorem N8k_single_apex_false
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment)
    {x : ℝ²} {i : Fin 3}
    (hx : N8SelectedApex S i x) :
    False := by
  set r := hx.radius with hr_def
  set m := S.moserCount x r with hm_def
  set s := S.sameCapCount i x r with hs_def
  set l := S.leftAdjCount i x r with hl_def
  set r_count := S.rightAdjCount i x r with hr_count_def
  have hcover : 4 ≤ m + s + l + r_count :=
    le_trans hx.selected_card (S.selected_le_groupSum i r hx.radius_pos)
  by_cases hl2 : 2 ≤ l
  ·
    classical
    have hwit : ∃ W : N8AdjacentArcWitness,
        W.base.apex = x ∧ W.base.selectedRadius = r ∧
          W.base.arc.support = S.leftAdjacentInteriorByIndex i :=
      S.exists_leftAdjacentArcWitness hN4e i hx.cap_mem r
    obtain ⟨W, hWapex, hWrad, hWsupp⟩ := hwit
    have hone := S.N8a3_adjacent_one_hit hN4e W
    rw [hWapex, hWrad, hWsupp] at hone
    have hge2 : 2 ≤ (SelectedClass A x r ∩ S.leftAdjacentInteriorByIndex i).card := by
      simpa [hl_def, FiniteEndpointShell.leftAdjCount] using hl2
    omega
  · by_cases hr2 : 2 ≤ r_count
    ·
      classical
      have hwit : ∃ W : N8AdjacentArcWitness,
          W.base.apex = x ∧ W.base.selectedRadius = r ∧
            W.base.arc.support = S.rightAdjacentInteriorByIndex i :=
        S.exists_rightAdjacentArcWitness hN4e i hx.cap_mem r
      obtain ⟨W, hWapex, hWrad, hWsupp⟩ := hwit
      have hone := S.N8a3_adjacent_one_hit hN4e W
      rw [hWapex, hWrad, hWsupp] at hone
      have hge2 : 2 ≤ (SelectedClass A x r ∩ S.rightAdjacentInteriorByIndex i).card := by
        simpa [hr_count_def, FiniteEndpointShell.rightAdjCount] using hr2
      omega
    · by_cases hm2 : 2 ≤ m
      ·
        have hm2_nat : 2 ≤ (SelectedClass A x r ∩ S.triangle.verts).card := hm2
        classical
        rcases Finset.exists_subset_card_eq (s := SelectedClass A x r ∩ S.triangle.verts) hm2_nat
          with ⟨E, hEsub, hEcard⟩
        rw [Finset.card_eq_two] at hEcard
        rcases hEcard with ⟨m₁, m₂, hm₁m₂_ne, hEeq⟩
        have hm₁_sel : m₁ ∈ SelectedClass A x r := by
          exact Finset.mem_of_mem_inter_left (hEsub (by simp [hEeq]))
        have hm₂_sel : m₂ ∈ SelectedClass A x r := by
          exact Finset.mem_of_mem_inter_left (hEsub (by simp [hEeq]))
        have hm₁_verts : m₁ ∈ S.triangle.verts := by
          exact Finset.mem_of_mem_inter_right (hEsub (by simp [hEeq]))
        have hm₂_verts : m₂ ∈ S.triangle.verts := by
          exact Finset.mem_of_mem_inter_right (hEsub (by simp [hEeq]))
        let hMoser2 : N8MoserEndpointPair S i x r :=
          { m₁ := m₁
            m₂ := m₂
            m₁_moser := hm₁_verts
            m₂_moser := hm₂_verts
            m₁_mem := hm₁_sel
            m₂_mem := hm₂_sel
            m₁_ne_m₂ := hm₁m₂_ne }
        by_cases hown :
            (m₁ = S.ownLeftEndpointByIndex i ∧ m₂ = S.ownRightEndpointByIndex i) ∨
            (m₁ = S.ownRightEndpointByIndex i ∧ m₂ = S.ownLeftEndpointByIndex i)
        ·
          classical
          have hl1 : l ≤ 1 := by omega
          have hr1 : r_count ≤ 1 := by omega
          have hs1 : s ≤ 1 := S.sameCapCount_le_one i r hx.cap_mem
          obtain ⟨_Wl, _, _, _⟩ := S.exists_leftAdjacentArcWitness hN4e i hx.cap_mem r
          obtain ⟨_Wr, _, _, _⟩ := S.exists_rightAdjacentArcWitness hN4e i hx.cap_mem r
          obtain ⟨_v₁, _v₂, _v₃, _, _, _, _, _hx1, _⟩ := S.exists_apexFrameData hN4e i hx.cap_mem
          have hm3 : m ≤ 3 := by
            simp only [hm_def, FiniteEndpointShell.moserCount]
            calc (SelectedClass A x r ∩ S.triangle.verts).card
                ≤ S.triangle.verts.card :=
                  Finset.card_le_card Finset.inter_subset_right
              _ = 3 := S.triangle.verts_card
          have hm_le2 : m ≤ 2 := by
            rw [hm_def]
            exact S.apexFrame_moserCount_le_two hN4e i hx.cap_mem r
          have hadj_l0 : l = 0 := by
            simp only [hl_def, FiniteEndpointShell.leftAdjCount]
            obtain ⟨d, hdpos, hC1, hC2, hC3⟩ := Erdos9796FiniteNine.circle_placement S hN4e
            have e12 : dist S.triangle.v1 S.triangle.v2 = d := hC1 _ S.CP.v2_mem_C1
            have e13 : dist S.triangle.v1 S.triangle.v3 = d := hC1 _ S.CP.v3_mem_C1
            have e23 : dist S.triangle.v2 S.triangle.v3 = d := hC2 _ S.CP.v3_mem_C2
            fin_cases i
            · simp only [leftAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
              simp only [ownLeftEndpointByIndex, ownRightEndpointByIndex] at hown
              have hv_right_sel : S.triangle.v3 ∈ SelectedClass A x r :=
                hown.elim (fun ⟨_, h2⟩ => h2 ▸ hm₂_sel) (fun ⟨h1, _⟩ => h1 ▸ hm₁_sel)
              have hx_cap : x ∈ S.I1 := by
                have h := hx.cap_mem; simp only [capInteriorByIndex] at h; exact h
              rw [I1, Finset.mem_erase, Finset.mem_erase] at hx_cap
              obtain ⟨hxv3, hxv2, hxC1⟩ := hx_cap
              have hxA : x ∈ A := S.CP.C1_subset hxC1
              have hncol : S.triangle.v3 ∉ affineSpan ℝ ({x, S.triangle.v2} : Set ℝ²) :=
                fun hmem => (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) S.triangle.v3_mem hxA S.triangle.v2_mem
                  hxv3.symm S.triangle.v23_ne.symm hxv2
                  (collinear_insert_of_mem_affineSpan_pair hmem)
              rw [Finset.card_eq_zero]; ext w
              simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
              intro hw_sel hw_I2
              have hw_C2 : w ∈ S.CP.C2 := by
                rw [I2, Finset.mem_erase, Finset.mem_erase] at hw_I2; exact hw_I2.2.2
              set s := affineSpan ℝ ({x, S.triangle.v2} : Set ℝ²)
              have hxs : x ∈ s := subset_affineSpan _ _ (by simp)
              have hv2s : S.triangle.v2 ∈ s := subset_affineSpan _ _ (by simp)
              haveI : Nonempty s := ⟨⟨x, hxs⟩⟩
              set o := EuclideanGeometry.reflection s S.triangle.v3
              have hv3_r : dist x S.triangle.v3 = r :=
                (mem_selectedClass.mp hv_right_sel).2
              have ho_r : dist x o = r :=
                (dist_reflection_eq_of_mem s hxs S.triangle.v3).trans hv3_r
              have ho_d : dist S.triangle.v2 o = d :=
                (dist_reflection_eq_of_mem s hv2s S.triangle.v3).trans e23
              have hv3_ne_o : S.triangle.v3 ≠ o := fun heq =>
                hncol ((reflection_eq_self_iff S.triangle.v3).mp heq.symm)
              rcases two_circle_common_point_eq_endpoint
                  (show (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨S.triangle.v2, d⟩ from
                    fun h => hxv2 (congrArg Sphere.center h))
                  hv3_ne_o
                  (mem_sphere.mpr (dist_comm x S.triangle.v3 ▸ hv3_r))
                  (mem_sphere.mpr (dist_comm x o ▸ ho_r))
                  (mem_sphere.mpr (dist_comm S.triangle.v2 S.triangle.v3 ▸ e23))
                  (mem_sphere.mpr (dist_comm S.triangle.v2 o ▸ ho_d))
                  (mem_sphere.mpr (dist_comm x w ▸ (mem_selectedClass.mp hw_sel).2))
                  (mem_sphere.mpr (dist_comm S.triangle.v2 w ▸ hC2 w hw_C2))
                with hwv3 | hwo
              · exact absurd (Finset.mem_of_mem_erase (hwv3 ▸ hw_I2)) (Finset.notMem_erase _ _)
              · exact absurd (hwo ▸ hw_I2)
                  (by
                      intro ho_I2
                      simp only [I2, mem_erase] at ho_I2
                      obtain ⟨ho_ne_v1, ho_ne_v3, ho_C2⟩ := ho_I2
                      have ho_A : o ∈ A := S.CP.C2_subset ho_C2
                      have hxv2_r : dist x S.triangle.v2 = r :=
                        hown.elim (fun ⟨h, _⟩ => h ▸ (mem_selectedClass.mp hm₁_sel).2)
                                  (fun ⟨_, h⟩ => h ▸ (mem_selectedClass.mp hm₂_sel).2)
                      have hmid : signedArea2 (midpoint ℝ S.triangle.v3 o) x S.triangle.v2 = 0 :=
                        twoCircle_midpoint_collinear (rq := r) (rv := d)
                          (by rw [dist_comm]; exact ho_r) (by rw [dist_comm]; exact hv3_r)
                          (by rw [dist_comm]; exact ho_d) (by rw [dist_comm]; exact e23)
                          hv3_ne_o.symm
                      have hsa : signedArea2 o x S.triangle.v2 = -signedArea2 x S.triangle.v2 S.triangle.v3 := by
                        have := signedArea2_reflection_neg (q := x) (v2 := S.triangle.v2)
                                   (y := S.triangle.v3) (u := o) hmid
                        have hcyc : signedArea2 S.triangle.v3 x S.triangle.v2 =
                            signedArea2 x S.triangle.v2 S.triangle.v3 := by simp only [signedArea2]; ring
                        rw [this, hcyc]
                      have hprop : dist x S.triangle.v2 ^ 2 * signedArea2 o S.triangle.v2 S.triangle.v3 =
                          dist S.triangle.v2 S.triangle.v3 ^ 2 * signedArea2 x S.triangle.v2 S.triangle.v3 :=
                        b3n9m084_angular_prop_dist x S.triangle.v2 S.triangle.v3 o
                          (by rw [hxv2_r, hv3_r]) (by rw [e23, ho_d])
                          (by rw [ho_r, hv3_r]) hsa
                      have hxC1_arc := (S.CP.arc_membership x hxA).1.mp hxC1
                      have hdxv2_sq : 0 < dist x S.triangle.v2 ^ 2 :=
                        sq_pos_of_pos (dist_pos.mpr hxv2)
                      have hd23_sq : 0 < dist S.triangle.v2 S.triangle.v3 ^ 2 := by
                        rw [e23]; exact sq_pos_of_pos hdpos
                      have hprod : signedArea2 o S.triangle.v2 S.triangle.v3 *
                          signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 ≤ 0 := by
                        have h1 : dist x S.triangle.v2 ^ 2 *
                            (signedArea2 o S.triangle.v2 S.triangle.v3 *
                             signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3) =
                            dist S.triangle.v2 S.triangle.v3 ^ 2 *
                            (signedArea2 x S.triangle.v2 S.triangle.v3 *
                             signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3) := by
                          linear_combination signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 * hprop
                        nlinarith only [h1, hd23_sq, hxC1_arc, hdxv2_sq, mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd23_sq) hxC1_arc]
                      have ho_C1 : o ∈ S.CP.C1 := (S.CP.arc_membership o ho_A).1.mpr hprod
                      by_cases hov : o ∈ S.triangle.verts
                      · simp only [MoserTriangle.verts] at hov
                        rcases mem_insert.mp hov with h | hov
                        · exact ho_ne_v1 h
                        · rcases mem_insert.mp hov with h | hov
                          · exact S.CP.v2_notin_C2 (h ▸ ho_C2)
                          · exact hv3_ne_o (mem_singleton.mp hov).symm
                      · have hone := S.CP.nonmoser_in_one o ho_A hov
                        simp only [ho_C1, ho_C2, ite_true, ite_false] at hone
                        omega)
            · simp only [leftAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
              simp only [ownLeftEndpointByIndex, ownRightEndpointByIndex] at hown
              have hv_right_sel : S.triangle.v1 ∈ SelectedClass A x r :=
                hown.elim (fun ⟨_, h2⟩ => h2 ▸ hm₂_sel) (fun ⟨h1, _⟩ => h1 ▸ hm₁_sel)
              have hx_cap : x ∈ S.I2 := by
                have h := hx.cap_mem; simp only [capInteriorByIndex] at h; exact h
              rw [I2, Finset.mem_erase, Finset.mem_erase] at hx_cap
              obtain ⟨hxv1, hxv3, hxC2⟩ := hx_cap
              have hxA : x ∈ A := S.CP.C2_subset hxC2
              have hncol : S.triangle.v1 ∉ affineSpan ℝ ({x, S.triangle.v3} : Set ℝ²) :=
                fun hmem => (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) S.triangle.v1_mem hxA S.triangle.v3_mem
                  hxv1.symm S.triangle.v13_ne hxv3
                  (collinear_insert_of_mem_affineSpan_pair hmem)
              rw [Finset.card_eq_zero]; ext w
              simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
              intro hw_sel hw_I3
              have hw_C3 : w ∈ S.CP.C3 := by
                rw [I3, Finset.mem_erase, Finset.mem_erase] at hw_I3; exact hw_I3.2.2
              set s := affineSpan ℝ ({x, S.triangle.v3} : Set ℝ²)
              have hxs : x ∈ s := subset_affineSpan _ _ (by simp)
              have hv3s : S.triangle.v3 ∈ s := subset_affineSpan _ _ (by simp)
              haveI : Nonempty s := ⟨⟨x, hxs⟩⟩
              set o := EuclideanGeometry.reflection s S.triangle.v1
              have hv1_r : dist x S.triangle.v1 = r :=
                (mem_selectedClass.mp hv_right_sel).2
              have hv1_d : dist S.triangle.v3 S.triangle.v1 = d := by
                rw [dist_comm]; exact e13
              have ho_r : dist x o = r :=
                (dist_reflection_eq_of_mem s hxs S.triangle.v1).trans hv1_r
              have ho_d : dist S.triangle.v3 o = d :=
                (dist_reflection_eq_of_mem s hv3s S.triangle.v1).trans hv1_d
              have hv1_ne_o : S.triangle.v1 ≠ o := fun heq =>
                hncol ((reflection_eq_self_iff S.triangle.v1).mp heq.symm)
              rcases two_circle_common_point_eq_endpoint
                  (show (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨S.triangle.v3, d⟩ from
                    fun h => hxv3 (congrArg Sphere.center h))
                  hv1_ne_o
                  (mem_sphere.mpr (dist_comm x S.triangle.v1 ▸ hv1_r))
                  (mem_sphere.mpr (dist_comm x o ▸ ho_r))
                  (mem_sphere.mpr (dist_comm S.triangle.v3 S.triangle.v1 ▸ hv1_d))
                  (mem_sphere.mpr (dist_comm S.triangle.v3 o ▸ ho_d))
                  (mem_sphere.mpr (dist_comm x w ▸ (mem_selectedClass.mp hw_sel).2))
                  (mem_sphere.mpr (dist_comm S.triangle.v3 w ▸ hC3 w hw_C3))
                with hwv1 | hwo
              · exact absurd (Finset.mem_of_mem_erase (hwv1 ▸ hw_I3)) (Finset.notMem_erase _ _)
              · exact absurd (hwo ▸ hw_I3)
                  (by
                      intro ho_I3
                      simp only [I3, mem_erase] at ho_I3
                      obtain ⟨ho_ne_v2, ho_ne_v1, ho_C3⟩ := ho_I3
                      have ho_A : o ∈ A := S.CP.C3_subset ho_C3
                      have hxv3_r : dist x S.triangle.v3 = r :=
                        hown.elim (fun ⟨h, _⟩ => h ▸ (mem_selectedClass.mp hm₁_sel).2)
                                  (fun ⟨_, h⟩ => h ▸ (mem_selectedClass.mp hm₂_sel).2)
                      have hmid : signedArea2 (midpoint ℝ S.triangle.v1 o) x S.triangle.v3 = 0 :=
                        twoCircle_midpoint_collinear (rq := r) (rv := d)
                          (by rw [dist_comm]; exact ho_r) (by rw [dist_comm]; exact hv1_r)
                          (by rw [dist_comm]; exact ho_d) (by rw [dist_comm]; exact hv1_d)
                          hv1_ne_o.symm
                      have hsa : signedArea2 o x S.triangle.v3 =
                          -signedArea2 x S.triangle.v3 S.triangle.v1 := by
                        have := signedArea2_reflection_neg (q := x) (v2 := S.triangle.v3)
                                   (y := S.triangle.v1) (u := o) hmid
                        have hcyc : signedArea2 S.triangle.v1 x S.triangle.v3 =
                            signedArea2 x S.triangle.v3 S.triangle.v1 := by
                          simp only [signedArea2]; ring
                        rw [this, hcyc]
                      have hprop : dist x S.triangle.v3 ^ 2 *
                          signedArea2 o S.triangle.v3 S.triangle.v1 =
                          dist S.triangle.v3 S.triangle.v1 ^ 2 *
                          signedArea2 x S.triangle.v3 S.triangle.v1 :=
                        b3n9m084_angular_prop_dist x S.triangle.v3 S.triangle.v1 o
                          (by rw [hxv3_r, hv1_r]) (by rw [hv1_d, ho_d])
                          (by rw [ho_r, hv1_r]) hsa
                      have hxC2_arc := (S.CP.arc_membership x hxA).2.1.mp hxC2
                      have hdxv3_sq : 0 < dist x S.triangle.v3 ^ 2 :=
                        sq_pos_of_pos (dist_pos.mpr hxv3)
                      have hd31_sq : 0 < dist S.triangle.v3 S.triangle.v1 ^ 2 := by
                        rw [hv1_d]; exact sq_pos_of_pos hdpos
                      have hprod : signedArea2 o S.triangle.v3 S.triangle.v1 *
                          signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 ≤ 0 := by
                        have h1 : dist x S.triangle.v3 ^ 2 *
                            (signedArea2 o S.triangle.v3 S.triangle.v1 *
                             signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1) =
                            dist S.triangle.v3 S.triangle.v1 ^ 2 *
                            (signedArea2 x S.triangle.v3 S.triangle.v1 *
                             signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1) := by
                          linear_combination
                            signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 * hprop
                        nlinarith only [h1, hd31_sq, hxC2_arc, hdxv3_sq, mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd31_sq) hxC2_arc]
                      have ho_C2 : o ∈ S.CP.C2 := (S.CP.arc_membership o ho_A).2.1.mpr hprod
                      by_cases hov : o ∈ S.triangle.verts
                      · simp only [MoserTriangle.verts] at hov
                        rcases mem_insert.mp hov with h | hov
                        · exact ho_ne_v1 h
                        · rcases mem_insert.mp hov with h | hov
                          · exact ho_ne_v2 h
                          · exact S.CP.v3_notin_C3 (mem_singleton.mp hov ▸ ho_C3)
                      · have hone := S.CP.nonmoser_in_one o ho_A hov
                        simp only [ho_C2, ho_C3, ite_true, ite_false] at hone
                        omega)
            · simp only [leftAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
              simp only [ownLeftEndpointByIndex, ownRightEndpointByIndex] at hown
              have hv_right_sel : S.triangle.v2 ∈ SelectedClass A x r :=
                hown.elim (fun ⟨_, h2⟩ => h2 ▸ hm₂_sel) (fun ⟨h1, _⟩ => h1 ▸ hm₁_sel)
              have hx_cap : x ∈ S.I3 := by
                have h := hx.cap_mem; simp only [capInteriorByIndex] at h; exact h
              rw [I3, Finset.mem_erase, Finset.mem_erase] at hx_cap
              obtain ⟨hxv2, hxv1, hxC3⟩ := hx_cap
              have hxA : x ∈ A := S.CP.C3_subset hxC3
              have hncol : S.triangle.v2 ∉ affineSpan ℝ ({x, S.triangle.v1} : Set ℝ²) :=
                fun hmem => (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) S.triangle.v2_mem hxA S.triangle.v1_mem
                  hxv2.symm S.triangle.v12_ne.symm hxv1
                  (collinear_insert_of_mem_affineSpan_pair hmem)
              rw [Finset.card_eq_zero]; ext w
              simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
              intro hw_sel hw_I1
              have hw_C1 : w ∈ S.CP.C1 := by
                rw [I1, Finset.mem_erase, Finset.mem_erase] at hw_I1; exact hw_I1.2.2
              set s := affineSpan ℝ ({x, S.triangle.v1} : Set ℝ²)
              have hxs : x ∈ s := subset_affineSpan _ _ (by simp)
              have hv1s : S.triangle.v1 ∈ s := subset_affineSpan _ _ (by simp)
              haveI : Nonempty s := ⟨⟨x, hxs⟩⟩
              set o := EuclideanGeometry.reflection s S.triangle.v2
              have hv2_r : dist x S.triangle.v2 = r :=
                (mem_selectedClass.mp hv_right_sel).2
              have ho_r : dist x o = r :=
                (dist_reflection_eq_of_mem s hxs S.triangle.v2).trans hv2_r
              have ho_d : dist S.triangle.v1 o = d :=
                (dist_reflection_eq_of_mem s hv1s S.triangle.v2).trans e12
              have hv2_ne_o : S.triangle.v2 ≠ o := fun heq =>
                hncol ((reflection_eq_self_iff S.triangle.v2).mp heq.symm)
              rcases two_circle_common_point_eq_endpoint
                  (show (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨S.triangle.v1, d⟩ from
                    fun h => hxv1 (congrArg Sphere.center h))
                  hv2_ne_o
                  (mem_sphere.mpr (dist_comm x S.triangle.v2 ▸ hv2_r))
                  (mem_sphere.mpr (dist_comm x o ▸ ho_r))
                  (mem_sphere.mpr (dist_comm S.triangle.v1 S.triangle.v2 ▸ e12))
                  (mem_sphere.mpr (dist_comm S.triangle.v1 o ▸ ho_d))
                  (mem_sphere.mpr (dist_comm x w ▸ (mem_selectedClass.mp hw_sel).2))
                  (mem_sphere.mpr (dist_comm S.triangle.v1 w ▸ hC1 w hw_C1))
                with hwv2 | hwo
              · exact absurd (Finset.mem_of_mem_erase (hwv2 ▸ hw_I1)) (Finset.notMem_erase _ _)
              · exact absurd (hwo ▸ hw_I1)
                  (by
                      intro ho_I1
                      simp only [I1, mem_erase] at ho_I1
                      obtain ⟨ho_ne_v3, ho_ne_v2, ho_C1⟩ := ho_I1
                      have ho_A : o ∈ A := S.CP.C1_subset ho_C1
                      have hxv1_r : dist x S.triangle.v1 = r :=
                        hown.elim (fun ⟨h, _⟩ => h ▸ (mem_selectedClass.mp hm₁_sel).2)
                                  (fun ⟨_, h⟩ => h ▸ (mem_selectedClass.mp hm₂_sel).2)
                      have hmid : signedArea2 (midpoint ℝ S.triangle.v2 o) x S.triangle.v1 = 0 :=
                        twoCircle_midpoint_collinear (rq := r) (rv := d)
                          (by rw [dist_comm]; exact ho_r) (by rw [dist_comm]; exact hv2_r)
                          (by rw [dist_comm]; exact ho_d) (by rw [dist_comm]; exact e12)
                          hv2_ne_o.symm
                      have hsa : signedArea2 o x S.triangle.v1 =
                          -signedArea2 x S.triangle.v1 S.triangle.v2 := by
                        have := signedArea2_reflection_neg (q := x) (v2 := S.triangle.v1)
                                   (y := S.triangle.v2) (u := o) hmid
                        have hcyc : signedArea2 S.triangle.v2 x S.triangle.v1 =
                            signedArea2 x S.triangle.v1 S.triangle.v2 := by
                          simp only [signedArea2]; ring
                        rw [this, hcyc]
                      have hprop : dist x S.triangle.v1 ^ 2 *
                          signedArea2 o S.triangle.v1 S.triangle.v2 =
                          dist S.triangle.v1 S.triangle.v2 ^ 2 *
                          signedArea2 x S.triangle.v1 S.triangle.v2 :=
                        b3n9m084_angular_prop_dist x S.triangle.v1 S.triangle.v2 o
                          (by rw [hxv1_r, hv2_r]) (by rw [e12, ho_d])
                          (by rw [ho_r, hv2_r]) hsa
                      have hxC3_arc := (S.CP.arc_membership x hxA).2.2.mp hxC3
                      have hdxv1_sq : 0 < dist x S.triangle.v1 ^ 2 :=
                        sq_pos_of_pos (dist_pos.mpr hxv1)
                      have hd12_sq : 0 < dist S.triangle.v1 S.triangle.v2 ^ 2 := by
                        rw [e12]; exact sq_pos_of_pos hdpos
                      have hprod : signedArea2 o S.triangle.v1 S.triangle.v2 *
                          signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 ≤ 0 := by
                        have h1 : dist x S.triangle.v1 ^ 2 *
                            (signedArea2 o S.triangle.v1 S.triangle.v2 *
                             signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2) =
                            dist S.triangle.v1 S.triangle.v2 ^ 2 *
                            (signedArea2 x S.triangle.v1 S.triangle.v2 *
                             signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2) := by
                          linear_combination
                            signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 * hprop
                        nlinarith only [h1, hd12_sq, hxC3_arc, hdxv1_sq, mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd12_sq) hxC3_arc]
                      have ho_C3 : o ∈ S.CP.C3 := (S.CP.arc_membership o ho_A).2.2.mpr hprod
                      by_cases hov : o ∈ S.triangle.verts
                      · simp only [MoserTriangle.verts] at hov
                        rcases mem_insert.mp hov with h | hov
                        · exact absurd (h ▸ ho_C1) S.CP.v1_notin_C1
                        · rcases mem_insert.mp hov with h | hov
                          · exact ho_ne_v2 h
                          · exact ho_ne_v3 (mem_singleton.mp hov)
                      · have hone := S.CP.nonmoser_in_one o ho_A hov
                        simp only [ho_C1, ho_C3, ite_true, ite_false] at hone
                        omega)
          have hadj_r0 : r_count = 0 := by
            simp only [hr_count_def, FiniteEndpointShell.rightAdjCount]
            obtain ⟨d, hdpos, hC1, hC2, hC3⟩ := Erdos9796FiniteNine.circle_placement S hN4e
            have e12 : dist S.triangle.v1 S.triangle.v2 = d := hC1 _ S.CP.v2_mem_C1
            have e13 : dist S.triangle.v1 S.triangle.v3 = d := hC1 _ S.CP.v3_mem_C1
            have e23 : dist S.triangle.v2 S.triangle.v3 = d := hC2 _ S.CP.v3_mem_C2
            fin_cases i
            · simp only [rightAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
              simp only [ownLeftEndpointByIndex, ownRightEndpointByIndex] at hown
              have hv_right_sel : S.triangle.v2 ∈ SelectedClass A x r :=
                hown.elim (fun ⟨h1, _⟩ => h1 ▸ hm₁_sel) (fun ⟨_, h2⟩ => h2 ▸ hm₂_sel)
              have hx_cap : x ∈ S.I1 := by
                have h := hx.cap_mem; simp only [capInteriorByIndex] at h; exact h
              rw [I1, Finset.mem_erase, Finset.mem_erase] at hx_cap
              obtain ⟨hxv3, hxv2, hxC1⟩ := hx_cap
              have hxA : x ∈ A := S.CP.C1_subset hxC1
              have hncol : S.triangle.v2 ∉ affineSpan ℝ ({x, S.triangle.v3} : Set ℝ²) :=
                fun hmem => (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) S.triangle.v2_mem hxA S.triangle.v3_mem
                  hxv2.symm S.triangle.v23_ne hxv3
                  (collinear_insert_of_mem_affineSpan_pair hmem)
              rw [Finset.card_eq_zero]; ext w
              simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
              intro hw_sel hw_I3
              have hw_C3 : w ∈ S.CP.C3 := by
                rw [I3, Finset.mem_erase, Finset.mem_erase] at hw_I3; exact hw_I3.2.2
              set s := affineSpan ℝ ({x, S.triangle.v3} : Set ℝ²)
              have hxs : x ∈ s := subset_affineSpan _ _ (by simp)
              have hv3s : S.triangle.v3 ∈ s := subset_affineSpan _ _ (by simp)
              haveI : Nonempty s := ⟨⟨x, hxs⟩⟩
              set o := EuclideanGeometry.reflection s S.triangle.v2
              have hv2_r : dist x S.triangle.v2 = r :=
                (mem_selectedClass.mp hv_right_sel).2
              have hv2_d : dist S.triangle.v3 S.triangle.v2 = d := by
                rw [dist_comm]; exact e23
              have ho_r : dist x o = r :=
                (dist_reflection_eq_of_mem s hxs S.triangle.v2).trans hv2_r
              have ho_d : dist S.triangle.v3 o = d :=
                (dist_reflection_eq_of_mem s hv3s S.triangle.v2).trans hv2_d
              have hv2_ne_o : S.triangle.v2 ≠ o := fun heq =>
                hncol ((reflection_eq_self_iff S.triangle.v2).mp heq.symm)
              rcases two_circle_common_point_eq_endpoint
                  (show (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨S.triangle.v3, d⟩ from
                    fun h => hxv3 (congrArg Sphere.center h))
                  hv2_ne_o
                  (mem_sphere.mpr (dist_comm x S.triangle.v2 ▸ hv2_r))
                  (mem_sphere.mpr (dist_comm x o ▸ ho_r))
                  (mem_sphere.mpr (dist_comm S.triangle.v3 S.triangle.v2 ▸ hv2_d))
                  (mem_sphere.mpr (dist_comm S.triangle.v3 o ▸ ho_d))
                  (mem_sphere.mpr (dist_comm x w ▸ (mem_selectedClass.mp hw_sel).2))
                  (mem_sphere.mpr (dist_comm S.triangle.v3 w ▸ hC3 w hw_C3))
                with hwv2 | hwo
              · exact absurd (hwv2 ▸ hw_I3) (Finset.notMem_erase _ _)
              · exact absurd (hwo ▸ hw_I3)
                  (by
                      intro ho_I3
                      simp only [I3, mem_erase] at ho_I3
                      obtain ⟨ho_ne_v2, ho_ne_v1, ho_C3⟩ := ho_I3
                      have ho_A : o ∈ A := S.CP.C3_subset ho_C3
                      have hxv3_r : dist x S.triangle.v3 = r :=
                        hown.elim (fun ⟨_, h⟩ => h ▸ (mem_selectedClass.mp hm₂_sel).2)
                                  (fun ⟨h, _⟩ => h ▸ (mem_selectedClass.mp hm₁_sel).2)
                      have hmid : signedArea2 (midpoint ℝ S.triangle.v2 o) x S.triangle.v3 = 0 :=
                        twoCircle_midpoint_collinear (rq := r) (rv := d)
                          (by rw [dist_comm]; exact ho_r) (by rw [dist_comm]; exact hv2_r)
                          (by rw [dist_comm]; exact ho_d) (by rw [dist_comm]; exact hv2_d)
                          hv2_ne_o.symm
                      have hsa : signedArea2 o x S.triangle.v3 =
                          -signedArea2 x S.triangle.v3 S.triangle.v2 := by
                        have := signedArea2_reflection_neg (q := x) (v2 := S.triangle.v3)
                                   (y := S.triangle.v2) (u := o) hmid
                        have hcyc : signedArea2 S.triangle.v2 x S.triangle.v3 =
                            signedArea2 x S.triangle.v3 S.triangle.v2 := by
                          simp only [signedArea2]; ring
                        rw [this, hcyc]
                      have hprop : dist x S.triangle.v3 ^ 2 *
                          signedArea2 o S.triangle.v2 S.triangle.v3 =
                          dist S.triangle.v3 S.triangle.v2 ^ 2 *
                          signedArea2 x S.triangle.v2 S.triangle.v3 := by
                        have hprop_swap := b3n9m084_angular_prop_dist x S.triangle.v3 S.triangle.v2 o
                          (by rw [hxv3_r, hv2_r]) (by rw [hv2_d, ho_d])
                          (by rw [ho_r, hv2_r]) hsa
                        have hs_o : signedArea2 o S.triangle.v3 S.triangle.v2 =
                            -signedArea2 o S.triangle.v2 S.triangle.v3 := by
                          simp only [signedArea2]; ring
                        have hs_x : signedArea2 x S.triangle.v3 S.triangle.v2 =
                            -signedArea2 x S.triangle.v2 S.triangle.v3 := by
                          simp only [signedArea2]; ring
                        rw [hs_o, hs_x] at hprop_swap; linarith
                      have hxC1_arc := (S.CP.arc_membership x hxA).1.mp hxC1
                      have hdxv3_sq : 0 < dist x S.triangle.v3 ^ 2 :=
                        sq_pos_of_pos (dist_pos.mpr hxv3)
                      have hd32_sq : 0 < dist S.triangle.v3 S.triangle.v2 ^ 2 := by
                        rw [hv2_d]; exact sq_pos_of_pos hdpos
                      have hprod : signedArea2 o S.triangle.v2 S.triangle.v3 *
                          signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 ≤ 0 := by
                        have h1 : dist x S.triangle.v3 ^ 2 *
                            (signedArea2 o S.triangle.v2 S.triangle.v3 *
                             signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3) =
                            dist S.triangle.v3 S.triangle.v2 ^ 2 *
                            (signedArea2 x S.triangle.v2 S.triangle.v3 *
                             signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3) := by
                          linear_combination
                            signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 * hprop
                        nlinarith only [h1, hd32_sq, hxC1_arc, hdxv3_sq, mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd32_sq) hxC1_arc]
                      have ho_C1 : o ∈ S.CP.C1 := (S.CP.arc_membership o ho_A).1.mpr hprod
                      by_cases hov : o ∈ S.triangle.verts
                      · simp only [MoserTriangle.verts] at hov
                        rcases mem_insert.mp hov with h | hov
                        · exact absurd (h ▸ ho_C1) S.CP.v1_notin_C1
                        · rcases mem_insert.mp hov with h | hov
                          · exact ho_ne_v2 h
                          · exact absurd (mem_singleton.mp hov ▸ ho_C3) S.CP.v3_notin_C3
                      · have hone := S.CP.nonmoser_in_one o ho_A hov
                        simp only [ho_C1, ho_C3, ite_true, ite_false] at hone
                        omega)
            · simp only [rightAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
              simp only [ownLeftEndpointByIndex, ownRightEndpointByIndex] at hown
              have hv_right_sel : S.triangle.v3 ∈ SelectedClass A x r :=
                hown.elim (fun ⟨h1, _⟩ => h1 ▸ hm₁_sel) (fun ⟨_, h2⟩ => h2 ▸ hm₂_sel)
              have hx_cap : x ∈ S.I2 := by
                have h := hx.cap_mem; simp only [capInteriorByIndex] at h; exact h
              rw [I2, Finset.mem_erase, Finset.mem_erase] at hx_cap
              obtain ⟨hxv1, hxv3, hxC2⟩ := hx_cap
              have hxA : x ∈ A := S.CP.C2_subset hxC2
              have hncol : S.triangle.v3 ∉ affineSpan ℝ ({x, S.triangle.v1} : Set ℝ²) :=
                fun hmem => (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) S.triangle.v3_mem hxA S.triangle.v1_mem
                  hxv3.symm S.triangle.v13_ne.symm hxv1
                  (collinear_insert_of_mem_affineSpan_pair hmem)
              rw [Finset.card_eq_zero]; ext w
              simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
              intro hw_sel hw_I1
              have hw_C1 : w ∈ S.CP.C1 := by
                rw [I1, Finset.mem_erase, Finset.mem_erase] at hw_I1; exact hw_I1.2.2
              set s := affineSpan ℝ ({x, S.triangle.v1} : Set ℝ²)
              have hxs : x ∈ s := subset_affineSpan _ _ (by simp)
              have hv1s : S.triangle.v1 ∈ s := subset_affineSpan _ _ (by simp)
              haveI : Nonempty s := ⟨⟨x, hxs⟩⟩
              set o := EuclideanGeometry.reflection s S.triangle.v3
              have hv3_r : dist x S.triangle.v3 = r :=
                (mem_selectedClass.mp hv_right_sel).2
              have hv3_d : dist S.triangle.v1 S.triangle.v3 = d := e13
              have ho_r : dist x o = r :=
                (dist_reflection_eq_of_mem s hxs S.triangle.v3).trans hv3_r
              have ho_d : dist S.triangle.v1 o = d :=
                (dist_reflection_eq_of_mem s hv1s S.triangle.v3).trans hv3_d
              have hv3_ne_o : S.triangle.v3 ≠ o := fun heq =>
                hncol ((reflection_eq_self_iff S.triangle.v3).mp heq.symm)
              rcases two_circle_common_point_eq_endpoint
                  (show (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨S.triangle.v1, d⟩ from
                    fun h => hxv1 (congrArg Sphere.center h))
                  hv3_ne_o
                  (mem_sphere.mpr (dist_comm x S.triangle.v3 ▸ hv3_r))
                  (mem_sphere.mpr (dist_comm x o ▸ ho_r))
                  (mem_sphere.mpr (dist_comm S.triangle.v1 S.triangle.v3 ▸ hv3_d))
                  (mem_sphere.mpr (dist_comm S.triangle.v1 o ▸ ho_d))
                  (mem_sphere.mpr (dist_comm x w ▸ (mem_selectedClass.mp hw_sel).2))
                  (mem_sphere.mpr (dist_comm S.triangle.v1 w ▸ hC1 w hw_C1))
                with hwv3 | hwo
              · exact absurd (hwv3 ▸ hw_I1) (Finset.notMem_erase _ _)
              · exact absurd (hwo ▸ hw_I1)
                  (by
                      intro ho_I1
                      simp only [I1, mem_erase] at ho_I1
                      obtain ⟨ho_ne_v3, ho_ne_v2, ho_C1⟩ := ho_I1
                      have ho_A : o ∈ A := S.CP.C1_subset ho_C1
                      have hxv1_r : dist x S.triangle.v1 = r :=
                        hown.elim (fun ⟨_, h⟩ => h ▸ (mem_selectedClass.mp hm₂_sel).2)
                                  (fun ⟨h, _⟩ => h ▸ (mem_selectedClass.mp hm₁_sel).2)
                      have hmid : signedArea2 (midpoint ℝ S.triangle.v3 o) x S.triangle.v1 = 0 :=
                        twoCircle_midpoint_collinear (rq := r) (rv := d)
                          (by rw [dist_comm]; exact ho_r) (by rw [dist_comm]; exact hv3_r)
                          (by rw [dist_comm]; exact ho_d) (by rw [dist_comm]; exact hv3_d)
                          hv3_ne_o.symm
                      have hsa : signedArea2 o x S.triangle.v1 =
                          -signedArea2 x S.triangle.v1 S.triangle.v3 := by
                        have := signedArea2_reflection_neg (q := x) (v2 := S.triangle.v1)
                                   (y := S.triangle.v3) (u := o) hmid
                        have hcyc : signedArea2 S.triangle.v3 x S.triangle.v1 =
                            signedArea2 x S.triangle.v1 S.triangle.v3 := by
                          simp only [signedArea2]; ring
                        rw [this, hcyc]
                      have hprop : dist x S.triangle.v1 ^ 2 *
                          signedArea2 o S.triangle.v3 S.triangle.v1 =
                          dist S.triangle.v1 S.triangle.v3 ^ 2 *
                          signedArea2 x S.triangle.v3 S.triangle.v1 := by
                        have hprop_swap := b3n9m084_angular_prop_dist x S.triangle.v1 S.triangle.v3 o
                          (by rw [hxv1_r, hv3_r]) (by rw [hv3_d, ho_d])
                          (by rw [ho_r, hv3_r]) hsa
                        have hs_o : signedArea2 o S.triangle.v1 S.triangle.v3 =
                            -signedArea2 o S.triangle.v3 S.triangle.v1 := by
                          simp only [signedArea2]; ring
                        have hs_x : signedArea2 x S.triangle.v1 S.triangle.v3 =
                            -signedArea2 x S.triangle.v3 S.triangle.v1 := by
                          simp only [signedArea2]; ring
                        rw [hs_o, hs_x] at hprop_swap; linarith
                      have hxC2_arc := (S.CP.arc_membership x hxA).2.1.mp hxC2
                      have hdxv1_sq : 0 < dist x S.triangle.v1 ^ 2 :=
                        sq_pos_of_pos (dist_pos.mpr hxv1)
                      have hd13_sq : 0 < dist S.triangle.v1 S.triangle.v3 ^ 2 := by
                        rw [hv3_d]; exact sq_pos_of_pos hdpos
                      have hprod : signedArea2 o S.triangle.v3 S.triangle.v1 *
                          signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 ≤ 0 := by
                        have h1 : dist x S.triangle.v1 ^ 2 *
                            (signedArea2 o S.triangle.v3 S.triangle.v1 *
                             signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1) =
                            dist S.triangle.v1 S.triangle.v3 ^ 2 *
                            (signedArea2 x S.triangle.v3 S.triangle.v1 *
                             signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1) := by
                          linear_combination
                            signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 * hprop
                        nlinarith only [h1, hd13_sq, hxC2_arc, hdxv1_sq, mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd13_sq) hxC2_arc]
                      have ho_C2 : o ∈ S.CP.C2 := (S.CP.arc_membership o ho_A).2.1.mpr hprod
                      by_cases hov : o ∈ S.triangle.verts
                      · simp only [MoserTriangle.verts] at hov
                        rcases mem_insert.mp hov with h | hov
                        · exact absurd (h ▸ ho_C1) S.CP.v1_notin_C1
                        · rcases mem_insert.mp hov with h | hov
                          · exact ho_ne_v2 h
                          · exact ho_ne_v3 (mem_singleton.mp hov)
                      · have hone := S.CP.nonmoser_in_one o ho_A hov
                        simp only [ho_C1, ho_C2, ite_true, ite_false] at hone
                        omega)
            · simp only [rightAdjacentInteriorByIndex, Fin.val_zero, Fin.val_one, Fin.val_two]
              simp only [ownLeftEndpointByIndex, ownRightEndpointByIndex] at hown
              have hv_right_sel : S.triangle.v1 ∈ SelectedClass A x r :=
                hown.elim (fun ⟨h1, _⟩ => h1 ▸ hm₁_sel) (fun ⟨_, h2⟩ => h2 ▸ hm₂_sel)
              have hx_cap : x ∈ S.I3 := by
                have h := hx.cap_mem; simp only [capInteriorByIndex] at h; exact h
              rw [I3, Finset.mem_erase, Finset.mem_erase] at hx_cap
              obtain ⟨hxv2, hxv1, hxC3⟩ := hx_cap
              have hxA : x ∈ A := S.CP.C3_subset hxC3
              have hncol : S.triangle.v1 ∉ affineSpan ℝ ({x, S.triangle.v2} : Set ℝ²) :=
                fun hmem => (_root_.Batch3N9.Problem97.ConvexIndep.not_three_collinear S.hconv) S.triangle.v1_mem hxA S.triangle.v2_mem
                  hxv1.symm S.triangle.v12_ne hxv2
                  (collinear_insert_of_mem_affineSpan_pair hmem)
              rw [Finset.card_eq_zero]; ext w
              simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
              intro hw_sel hw_I2
              have hw_C2 : w ∈ S.CP.C2 := by
                rw [I2, Finset.mem_erase, Finset.mem_erase] at hw_I2; exact hw_I2.2.2
              set s := affineSpan ℝ ({x, S.triangle.v2} : Set ℝ²)
              have hxs : x ∈ s := subset_affineSpan _ _ (by simp)
              have hv2s : S.triangle.v2 ∈ s := subset_affineSpan _ _ (by simp)
              haveI : Nonempty s := ⟨⟨x, hxs⟩⟩
              set o := EuclideanGeometry.reflection s S.triangle.v1
              have hv1_r : dist x S.triangle.v1 = r :=
                (mem_selectedClass.mp hv_right_sel).2
              have hv1_d : dist S.triangle.v2 S.triangle.v1 = d := by
                rw [dist_comm]; exact e12
              have ho_r : dist x o = r :=
                (dist_reflection_eq_of_mem s hxs S.triangle.v1).trans hv1_r
              have ho_d : dist S.triangle.v2 o = d :=
                (dist_reflection_eq_of_mem s hv2s S.triangle.v1).trans hv1_d
              have hv1_ne_o : S.triangle.v1 ≠ o := fun heq =>
                hncol ((reflection_eq_self_iff S.triangle.v1).mp heq.symm)
              rcases two_circle_common_point_eq_endpoint
                  (show (⟨x, r⟩ : Sphere ℝ²) ≠ ⟨S.triangle.v2, d⟩ from
                    fun h => hxv2 (congrArg Sphere.center h))
                  hv1_ne_o
                  (mem_sphere.mpr (dist_comm x S.triangle.v1 ▸ hv1_r))
                  (mem_sphere.mpr (dist_comm x o ▸ ho_r))
                  (mem_sphere.mpr (dist_comm S.triangle.v2 S.triangle.v1 ▸ hv1_d))
                  (mem_sphere.mpr (dist_comm S.triangle.v2 o ▸ ho_d))
                  (mem_sphere.mpr (dist_comm x w ▸ (mem_selectedClass.mp hw_sel).2))
                  (mem_sphere.mpr (dist_comm S.triangle.v2 w ▸ hC2 w hw_C2))
                with hwv1 | hwo
              · exact absurd (hwv1 ▸ hw_I2) (Finset.notMem_erase _ _)
              · exact absurd (hwo ▸ hw_I2)
                  (by
                      intro ho_I2
                      simp only [I2, mem_erase] at ho_I2
                      obtain ⟨ho_ne_v1, ho_ne_v3, ho_C2⟩ := ho_I2
                      have ho_A : o ∈ A := S.CP.C2_subset ho_C2
                      have hxv2_r : dist x S.triangle.v2 = r :=
                        hown.elim (fun ⟨_, h⟩ => h ▸ (mem_selectedClass.mp hm₂_sel).2)
                                  (fun ⟨h, _⟩ => h ▸ (mem_selectedClass.mp hm₁_sel).2)
                      have hmid : signedArea2 (midpoint ℝ S.triangle.v1 o) x S.triangle.v2 = 0 :=
                        twoCircle_midpoint_collinear (rq := r) (rv := d)
                          (by rw [dist_comm]; exact ho_r) (by rw [dist_comm]; exact hv1_r)
                          (by rw [dist_comm]; exact ho_d) (by rw [dist_comm]; exact hv1_d)
                          hv1_ne_o.symm
                      have hsa : signedArea2 o x S.triangle.v2 =
                          -signedArea2 x S.triangle.v2 S.triangle.v1 := by
                        have := signedArea2_reflection_neg (q := x) (v2 := S.triangle.v2)
                                   (y := S.triangle.v1) (u := o) hmid
                        have hcyc : signedArea2 S.triangle.v1 x S.triangle.v2 =
                            signedArea2 x S.triangle.v2 S.triangle.v1 := by
                          simp only [signedArea2]; ring
                        rw [this, hcyc]
                      have hprop : dist x S.triangle.v2 ^ 2 *
                          signedArea2 o S.triangle.v1 S.triangle.v2 =
                          dist S.triangle.v2 S.triangle.v1 ^ 2 *
                          signedArea2 x S.triangle.v1 S.triangle.v2 := by
                        have hprop_swap := b3n9m084_angular_prop_dist x S.triangle.v2 S.triangle.v1 o
                          (by rw [hxv2_r, hv1_r]) (by rw [hv1_d, ho_d])
                          (by rw [ho_r, hv1_r]) hsa
                        have hs_o : signedArea2 o S.triangle.v2 S.triangle.v1 =
                            -signedArea2 o S.triangle.v1 S.triangle.v2 := by
                          simp only [signedArea2]; ring
                        have hs_x : signedArea2 x S.triangle.v2 S.triangle.v1 =
                            -signedArea2 x S.triangle.v1 S.triangle.v2 := by
                          simp only [signedArea2]; ring
                        rw [hs_o, hs_x] at hprop_swap; linarith
                      have hxC3_arc := (S.CP.arc_membership x hxA).2.2.mp hxC3
                      have hdxv2_sq : 0 < dist x S.triangle.v2 ^ 2 :=
                        sq_pos_of_pos (dist_pos.mpr hxv2)
                      have hd21_sq : 0 < dist S.triangle.v2 S.triangle.v1 ^ 2 := by
                        rw [hv1_d]; exact sq_pos_of_pos hdpos
                      have hprod : signedArea2 o S.triangle.v1 S.triangle.v2 *
                          signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 ≤ 0 := by
                        have h1 : dist x S.triangle.v2 ^ 2 *
                            (signedArea2 o S.triangle.v1 S.triangle.v2 *
                             signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2) =
                            dist S.triangle.v2 S.triangle.v1 ^ 2 *
                            (signedArea2 x S.triangle.v1 S.triangle.v2 *
                             signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2) := by
                          linear_combination
                            signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 * hprop
                        nlinarith only [h1, hd21_sq, hxC3_arc, hdxv2_sq, mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd21_sq) hxC3_arc]
                      have ho_C3 : o ∈ S.CP.C3 := (S.CP.arc_membership o ho_A).2.2.mpr hprod
                      by_cases hov : o ∈ S.triangle.verts
                      · simp only [MoserTriangle.verts] at hov
                        rcases mem_insert.mp hov with h | hov
                        · exact ho_ne_v1 h
                        · rcases mem_insert.mp hov with h | hov
                          · exact absurd (h ▸ ho_C2) S.CP.v2_notin_C2
                          · exact ho_ne_v3 (mem_singleton.mp hov)
                      · have hone := S.CP.nonmoser_in_one o ho_A hov
                        simp only [ho_C2, ho_C3, ite_true, ite_false] at hone
                        omega)
          omega
        ·
          exact S.N8b_endpoint_pair_split hN4e hx hMoser2 hown
      ·
        classical
        have hpos : 0 < (SelectedClass A x r).card :=
          lt_of_lt_of_le (by norm_num) hx.selected_card
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        have hxv : dist x v = r := (mem_selectedClass.mp hv).2
        let hx_pkt : S.N8SameCapClassPacket hN4e x i :=
          { center := v
            radius := r
            radius_pos := hx.radius_pos
            x_on_selected_circle := hxv }
        by_cases hCapCenter : Nonempty (S.N8iCapCenterPacket hx_pkt)
        ·
          obtain ⟨hi⟩ := hCapCenter
          exact S.N8i_capcenter_fullwidth_false hN4e hx_pkt hi
        ·
          have hm1 : m ≤ 1 := by omega
          have hl1 : l ≤ 1 := by omega
          have hr1 : r_count ≤ 1 := by omega
          have hs1le : s ≤ 1 := S.sameCapCount_le_one i r hx.cap_mem
          have hs1 : 1 ≤ s := by omega
          have hl1ge : 1 ≤ l := by omega
          have hr1ge : 1 ≤ r_count := by omega
          have hm1ge : 1 ≤ m := by omega
          have hmc : (SelectedClass A x r ∩ S.triangle.verts).card = 1 := by
            have : m = 1 := le_antisymm hm1 hm1ge
            simpa [hm_def, FiniteEndpointShell.moserCount] using this
          have hl1geC : 1 ≤ (SelectedClass A x r ∩ S.leftAdjacentInteriorByIndex i).card := by
            simpa [hl_def, FiniteEndpointShell.leftAdjCount] using hl1ge
          have hr1geC : 1 ≤ (SelectedClass A x r ∩ S.rightAdjacentInteriorByIndex i).card := by
            simpa [hr_count_def, FiniteEndpointShell.rightAdjCount] using hr1ge
          exact S.b3n9m084_m1_branch_false hN4e hx.cap_mem hx.radius_pos hmc hl1geC hr1geC
theorem N8k_capInterior_false_of_hasNEquidistantProperty
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment)
    (hK4 : HasNEquidistantProperty 4 A)
    {x : ℝ²} {i : Fin 3}
    (hxcap : x ∈ S.capInteriorByIndex i) :
    False := by
  rcases N8SelectedApex.nonempty_of_hasNEquidistantProperty
      (S := S) (i := i) (x := x) hK4 hxcap with ⟨hx⟩
  exact S.N8k_single_apex_false hN4e hx
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit084

open scoped EuclideanGeometry

theorem solution {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A)
    (hN4e : S.N4eCapContainment)
    (hK4 : Batch3N9.Problem97.HasNEquidistantProperty 4 A)
    {x : ℝ²} {i : Fin 3} (hxcap : x ∈ S.capInteriorByIndex i) :
    False := by
  exact S.N8k_capInterior_false_of_hasNEquidistantProperty hN4e hK4 hxcap
