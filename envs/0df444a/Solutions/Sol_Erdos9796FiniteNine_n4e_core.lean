-- Prove2me | solution 1 for Erdos9796FiniteNine.n4e_core
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T01:51:48.751714+00:00
-- url     : https://prove2.me/submissions/1a2e8096-87cf-4595-b748-0c0ada857b8a

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N4dPackets
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

-- Original module: Solutions.Batch3N9.N4d.TrackBPilotSupport
section Batch3N9Unit050
namespace Batch3N9
open scoped EuclideanGeometry
open EuclideanGeometry
namespace Problem97
end Problem97
end Batch3N9
end Batch3N9Unit050

-- Original module: Solutions.Batch3N9.N9Endpoint.N4e
section Batch3N9Unit051
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
theorem I1_card_eq_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.I1.card = 2 := by
  have hI1 : S.I1.card + 2 = S.CP.C1.card := S.I1_card
  have hC1 : S.CP.C1.card = 4 := (S.n5_forced_m44).1
  omega
theorem I2_card_eq_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.I2.card = 2 := by
  have hI2 : S.I2.card + 2 = S.CP.C2.card := S.I2_card
  have hC2 : S.CP.C2.card = 4 := (S.n5_forced_m44).2.1
  omega
theorem I3_card_eq_two
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.I3.card = 2 := by
  have hI3 : S.I3.card + 2 = S.CP.C3.card := S.I3_card
  have hC3 : S.CP.C3.card = 4 := (S.n5_forced_m44).2.2
  omega
noncomputable def zeroDefectCapLayout
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    ZeroDefectCapLayout (S := S) := by
  classical
  have hI1 : ∃ x y : ℝ², x ≠ y ∧ S.I1 = ({x, y} : Finset ℝ²) := by
    simpa [Finset.card_eq_two] using S.I1_card_eq_two
  have hI2 : ∃ x y : ℝ², x ≠ y ∧ S.I2 = ({x, y} : Finset ℝ²) := by
    simpa [Finset.card_eq_two] using S.I2_card_eq_two
  have hI3 : ∃ x y : ℝ², x ≠ y ∧ S.I3 = ({x, y} : Finset ℝ²) := by
    simpa [Finset.card_eq_two] using S.I3_card_eq_two
  choose a1 b1 hab1 hI1eq using hI1
  choose a2 b2 hab2 hI2eq using hI2
  choose a3 b3 hab3 hI3eq using hI3
  exact ⟨a1, b1, a2, b2, a3, b3, hI1eq, hI2eq, hI3eq⟩
theorem b3n9m051_witnessClassAt_v1_sideBounds
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ} :
    ((S.witnessClassAt_v1 r) ∩ S.CP.C2).card ≤ 1
      ∧ ((S.witnessClassAt_v1 r) ∩ S.CP.C3).card ≤ 1 := by
  classical
  constructor
  · apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v3_of_supportCap
      (A := A) (C := S.CP.C2) (M := S.triangle2)
      S.hconv S.hnoncol S.CP.C2_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.1)
      S.CP.v3_mem_C2 S.CP.v1_mem_C2 S.packet2 S.packet2.inner_at_v1
      (S := (S.witnessClassAt_v1 r) ∩ S.CP.C2) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
  · apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v2_of_supportCap
      (A := A) (C := S.CP.C3) (M := S.triangle3)
      S.hconv S.hnoncol S.CP.C3_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.2)
      S.CP.v1_mem_C3 S.CP.v2_mem_C3 S.packet3 S.packet3.inner_at_v1
      (S := (S.witnessClassAt_v1 r) ∩ S.CP.C3) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
theorem b3n9m051_witnessClassAt_v2_sideBounds
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ} :
    ((S.witnessClassAt_v2 r) ∩ S.CP.C1).card ≤ 1
      ∧ ((S.witnessClassAt_v2 r) ∩ S.CP.C3).card ≤ 1 := by
  classical
  constructor
  · apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v2_of_supportCap
      (A := A) (C := S.CP.C1) (M := S.triangle)
      S.hconv S.hnoncol S.CP.C1_subset
      (fun x hxA => (S.CP.arc_membership x hxA).1)
      S.CP.v2_mem_C1 S.CP.v3_mem_C1 S.Packet S.Packet.inner_at_v1
      (S := (S.witnessClassAt_v2 r) ∩ S.CP.C1) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
  · apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v3_of_supportCap
      (A := A) (C := S.CP.C3) (M := S.triangle3)
      S.hconv S.hnoncol S.CP.C3_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.2)
      S.CP.v1_mem_C3 S.CP.v2_mem_C3 S.packet3 S.packet3.inner_at_v1
      (S := (S.witnessClassAt_v2 r) ∩ S.CP.C3) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
theorem b3n9m051_witnessClassAt_v3_sideBounds
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ} :
    ((S.witnessClassAt_v3 r) ∩ S.CP.C1).card ≤ 1
      ∧ ((S.witnessClassAt_v3 r) ∩ S.CP.C2).card ≤ 1 := by
  classical
  constructor
  · apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v3_of_supportCap
      (A := A) (C := S.CP.C1) (M := S.triangle)
      S.hconv S.hnoncol S.CP.C1_subset
      (fun x hxA => (S.CP.arc_membership x hxA).1)
      S.CP.v2_mem_C1 S.CP.v3_mem_C1 S.Packet S.Packet.inner_at_v1
      (S := (S.witnessClassAt_v3 r) ∩ S.CP.C1) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
  · apply Problem97.FiniteEndpoint.one_hit_sameRadius_at_v2_of_supportCap
      (A := A) (C := S.CP.C2) (M := S.triangle2)
      S.hconv S.hnoncol S.CP.C2_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.1)
      S.CP.v3_mem_C2 S.CP.v1_mem_C2 S.packet2 S.packet2.inner_at_v1
      (S := (S.witnessClassAt_v3 r) ∩ S.CP.C2) (r := r)
    · exact Finset.inter_subset_right
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hx)).2
theorem coreSelector_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v1 r).card) :
    (S.witnessClassAt_v1 r).card = 4 ∧
      S.I1 ⊆ S.witnessClassAt_v1 r ∧
      ((S.witnessClassAt_v1 r) ∩ S.CP.C2).card ≤ 1 ∧
      ((S.witnessClassAt_v1 r) ∩ S.CP.C3).card ≤ 1 := by
  classical
  let T : Finset ℝ² := S.witnessClassAt_v1 r
  have hside := S.b3n9m051_witnessClassAt_v1_sideBounds (r := r)
  rcases hside with ⟨hC2_one, hC3_one⟩
  have hcardT : 4 ≤ T.card := by simpa [T] using hcard
  have hC2_oneT : (T ∩ S.CP.C2).card ≤ 1 := by simpa [T] using hC2_one
  have hC3_oneT : (T ∩ S.CP.C3).card ≤ 1 := by simpa [T] using hC3_one
  have hv1_not_mem_T : S.triangle.v1 ∉ T := by
    intro hv1T
    have hv1eq : dist S.triangle.v1 S.triangle.v1 = r := (Finset.mem_filter.mp hv1T).2
    have h0r : (0 : ℝ) = r := by simpa using hv1eq
    nlinarith only [hr, h0r]
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
    simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I1
  have hinter_le : (T ∩ S.I1).card ≤ S.I1.card := Finset.card_le_card Finset.inter_subset_right
  have hI1_two : S.I1.card = 2 := S.I1_card_eq_two
  have hT_le_four : T.card ≤ 4 := by
    omega
  have hT_eq_four : T.card = 4 := by
    omega
  have hinter_ge : S.I1.card ≤ (T ∩ S.I1).card := by
    omega
  have hI1eq : T ∩ S.I1 = S.I1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hinter_ge
  have hI1sub : S.I1 ⊆ T := by
    intro x hx
    have : x ∈ T ∩ S.I1 := by simpa [hI1eq] using hx
    exact Finset.mem_of_mem_inter_left this
  exact ⟨hT_eq_four, hI1sub, hC2_oneT, hC3_oneT⟩
theorem coreSelector_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v2 r).card) :
    (S.witnessClassAt_v2 r).card = 4 ∧
      S.I2 ⊆ S.witnessClassAt_v2 r ∧
      ((S.witnessClassAt_v2 r) ∩ S.CP.C1).card ≤ 1 ∧
      ((S.witnessClassAt_v2 r) ∩ S.CP.C3).card ≤ 1 := by
  classical
  let T : Finset ℝ² := S.witnessClassAt_v2 r
  have hside := S.b3n9m051_witnessClassAt_v2_sideBounds (r := r)
  rcases hside with ⟨hC1_one, hC3_one⟩
  have hcardT : 4 ≤ T.card := by simpa [T] using hcard
  have hC1_oneT : (T ∩ S.CP.C1).card ≤ 1 := by simpa [T] using hC1_one
  have hC3_oneT : (T ∩ S.CP.C3).card ≤ 1 := by simpa [T] using hC3_one
  have hv2_not_mem_T : S.triangle.v2 ∉ T := by
    intro hv2T
    have hv2eq : dist S.triangle.v2 S.triangle.v2 = r := (Finset.mem_filter.mp hv2T).2
    have h0r : (0 : ℝ) = r := by simpa using hv2eq
    nlinarith only [hr, h0r]
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
    simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I2
  have hinter_le : (T ∩ S.I2).card ≤ S.I2.card := Finset.card_le_card Finset.inter_subset_right
  have hI2_two : S.I2.card = 2 := S.I2_card_eq_two
  have hT_eq_four : T.card = 4 := by
    omega
  have hinter_ge : S.I2.card ≤ (T ∩ S.I2).card := by
    omega
  have hI2eq : T ∩ S.I2 = S.I2 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hinter_ge
  have hI2sub : S.I2 ⊆ T := by
    intro x hx
    have : x ∈ T ∩ S.I2 := by simpa [hI2eq] using hx
    exact Finset.mem_of_mem_inter_left this
  exact ⟨hT_eq_four, hI2sub, hC1_oneT, hC3_oneT⟩
theorem coreSelector_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v3 r).card) :
    (S.witnessClassAt_v3 r).card = 4 ∧
      S.I3 ⊆ S.witnessClassAt_v3 r ∧
      ((S.witnessClassAt_v3 r) ∩ S.CP.C1).card ≤ 1 ∧
      ((S.witnessClassAt_v3 r) ∩ S.CP.C2).card ≤ 1 := by
  classical
  let T : Finset ℝ² := S.witnessClassAt_v3 r
  have hside := S.b3n9m051_witnessClassAt_v3_sideBounds (r := r)
  rcases hside with ⟨hC1_one, hC2_one⟩
  have hcardT : 4 ≤ T.card := by simpa [T] using hcard
  have hC1_oneT : (T ∩ S.CP.C1).card ≤ 1 := by simpa [T] using hC1_one
  have hC2_oneT : (T ∩ S.CP.C2).card ≤ 1 := by simpa [T] using hC2_one
  have hv3_not_mem_T : S.triangle.v3 ∉ T := by
    intro hv3T
    have hv3eq : dist S.triangle.v3 S.triangle.v3 = r := (Finset.mem_filter.mp hv3T).2
    have h0r : (0 : ℝ) = r := by simpa using hv3eq
    nlinarith only [hr, h0r]
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
    simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I3
  have hinter_le : (T ∩ S.I3).card ≤ S.I3.card := Finset.card_le_card Finset.inter_subset_right
  have hI3_two : S.I3.card = 2 := S.I3_card_eq_two
  have hT_eq_four : T.card = 4 := by
    omega
  have hinter_ge : S.I3.card ≤ (T ∩ S.I3).card := by
    omega
  have hI3eq : T ∩ S.I3 = S.I3 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hinter_ge
  have hI3sub : S.I3 ⊆ T := by
    intro x hx
    have : x ∈ T ∩ S.I3 := by simpa [hI3eq] using hx
    exact Finset.mem_of_mem_inter_left this
  exact ⟨hT_eq_four, hI3sub, hC1_oneT, hC2_oneT⟩
theorem formB_v1_split
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r : ℝ}
    (hB : S.IsFormB_v1 r) :
    (∃ h : (Z.a2 : ℝ²) ∈ S.I2,
        S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²)) ∨
      (∃ h : (Z.b2 : ℝ²) ∈ S.I2,
        S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²)) := by
  rcases hB with ⟨x, hxI2, hxeq, -⟩
  have hxmem : x ∈ ({Z.a2, Z.b2} : Finset ℝ²) := by
    rw [← Z.hI2]
    simpa using hxI2
  rcases Finset.mem_insert.mp hxmem with rfl | hx
  · exact Or.inl ⟨by simpa [Z.hI2] using hxI2, hxeq⟩
  · have : x = Z.b2 := by simpa using hx
    subst this
    exact Or.inr ⟨by simpa [Z.hI2] using hxI2, hxeq⟩
theorem formC_v1_split
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r : ℝ}
    (hC : S.IsFormC_v1 r) :
    (∃ h : (Z.a3 : ℝ²) ∈ S.I3,
        S.witnessClassAt_v1 r ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
      (∃ h : (Z.b3 : ℝ²) ∈ S.I3,
        S.witnessClassAt_v1 r ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²)) := by
  rcases hC with ⟨y, hyI3, -, hyeq⟩
  have hymem : y ∈ ({Z.a3, Z.b3} : Finset ℝ²) := by
    rw [← Z.hI3]
    simpa using hyI3
  rcases Finset.mem_insert.mp hymem with rfl | hy
  · exact Or.inl ⟨by simpa [Z.hI3] using hyI3, hyeq⟩
  · have : y = Z.b3 := by simpa using hy
    subst this
    exact Or.inr ⟨by simpa [Z.hI3] using hyI3, hyeq⟩
theorem selectorShape_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) :
    ∃ r : ℝ, 0 < r ∧
      let T := S.witnessClassAt_v2 r
      T.card = 4 ∧
      S.I2 ⊆ T ∧
      ∃ p q : ℝ²,
        p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) ∧
        q ∈ ({Z.a3, Z.b3, S.triangle.v1} : Finset ℝ²) ∧
        T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
        T ∩ S.CP.C3 = ({q} : Finset ℝ²) := by
  classical
  rcases S.k4_at_v2 with ⟨r, hr, hcard⟩
  let T : Finset ℝ² := S.witnessClassAt_v2 r
  have hcore := S.coreSelector_v2 hr hcard
  rcases hcore with ⟨hTcard, hI2sub, hC1le, hC3le⟩
  have hTcard' : T.card = 4 := by simpa [T] using hTcard
  have hC1le' : (T ∩ S.CP.C1).card ≤ 1 := by simpa [T] using hC1le
  have hC3le' : (T ∩ S.CP.C3).card ≤ 1 := by simpa [T] using hC3le
  have hv2notT : S.triangle.v2 ∉ T := by
    intro hv2T
    have hv2eq : dist S.triangle.v2 S.triangle.v2 = r := (Finset.mem_filter.mp hv2T).2
    have h0r : (0 : ℝ) = r := by simpa using hv2eq
    nlinarith only [hr, h0r]
  have hI2two : S.I2.card = 2 := S.I2_card_eq_two
  have hI2sub' : S.I2 ⊆ T ∩ S.I2 := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hI2sub hz, hz⟩
  have hTminus_eq_two : (T \ S.I2).card = 2 := by
    have hsplit : (T \ S.I2).card + (T ∩ S.I2).card = T.card := by
      simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I2
    have hI2ge : S.I2.card ≤ (T ∩ S.I2).card := Finset.card_le_card hI2sub'
    have hI2le : (T ∩ S.I2).card ≤ S.I2.card := Finset.card_le_card Finset.inter_subset_right
    omega
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
    · exact False.elim (hv2notT (hxv2 ▸ hxT))
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
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxT, hxC1⟩))
    · have hxC3 : x ∈ S.CP.C3 := by
        by_cases hxC3 : x ∈ S.CP.C3
        · exact hxC3
        · have : (0 : ℕ) = 1 := by
            simpa [hxC1, hxnotC2, hxC3] using hone
          omega
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hxT, hxC3⟩))
  have hUnion_eq_two :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card = 2 := by
    have hTminus_le : (T \ S.I2).card ≤ ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card :=
      Finset.card_le_card hcover
    have hUnion_le :
        ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card ≤ 2 := by
      calc
        ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card
            ≤ (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
        _ ≤ 1 + 1 := by omega
        _ = 2 := by norm_num
    omega
  have hsum_eq_two : (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card = 2 := by
    have hUnion_le_sum : ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card ≤
        (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
    omega
  have hC1eq1 : (T ∩ S.CP.C1).card = 1 := by omega
  have hC3eq1 : (T ∩ S.CP.C3).card = 1 := by omega
  obtain ⟨p, hpeq⟩ := Finset.card_eq_one.mp hC1eq1
  obtain ⟨q, hqeq⟩ := Finset.card_eq_one.mp hC3eq1
  have hpT : p ∈ T := by
    have hpmem : p ∈ ({p} : Finset ℝ²) := by simp
    rw [← hpeq] at hpmem
    exact (Finset.mem_inter.mp hpmem).1
  have hqT : q ∈ T := by
    have hqmem : q ∈ ({q} : Finset ℝ²) := by simp
    rw [← hqeq] at hqmem
    exact (Finset.mem_inter.mp hqmem).1
  have hpC1 : p ∈ S.CP.C1 := by
    have hpmem : p ∈ ({p} : Finset ℝ²) := by simp
    rw [← hpeq] at hpmem
    exact (Finset.mem_inter.mp hpmem).2
  have hqC3 : q ∈ S.CP.C3 := by
    have hqmem : q ∈ ({q} : Finset ℝ²) := by simp
    rw [← hqeq] at hqmem
    exact (Finset.mem_inter.mp hqmem).2
  have hp_ne_v2 : p ≠ S.triangle.v2 := by
    intro h
    exact hv2notT (h ▸ hpT)
  have hq_ne_v2 : q ≠ S.triangle.v2 := by
    intro h
    exact hv2notT (h ▸ hqT)
  have hp_named : p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) := by
    by_cases hpv3 : p = S.triangle.v3
    · simp [hpv3]
    · have hpI1 : p ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hpv3, Finset.mem_erase.mpr ⟨hp_ne_v2, hpC1⟩⟩
      have hpI1' : p ∈ ({Z.a1, Z.b1} : Finset ℝ²) := by
        have : p ∈ S.I1 := hpI1
        rw [Z.hI1] at this
        exact this
      rcases Finset.mem_insert.mp hpI1' with hpa1 | hpb1
      · simp [hpa1]
      · have hpb1' : p = Z.b1 := by simpa using hpb1
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hpb1')))
  have hq_named : q ∈ ({Z.a3, Z.b3, S.triangle.v1} : Finset ℝ²) := by
    by_cases hqv1 : q = S.triangle.v1
    · simp [hqv1]
    · have hqI3 : q ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hq_ne_v2, Finset.mem_erase.mpr ⟨hqv1, hqC3⟩⟩
      have hqI3' : q ∈ ({Z.a3, Z.b3} : Finset ℝ²) := by
        have : q ∈ S.I3 := hqI3
        rw [Z.hI3] at this
        exact this
      rcases Finset.mem_insert.mp hqI3' with hqa3 | hqb3
      · simp [hqa3]
      · have hqb3' : q = Z.b3 := by simpa using hqb3
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hqb3')))
  refine ⟨r, hr, ?_⟩
  dsimp [T]
  exact ⟨hTcard, hI2sub, p, q, hp_named, hq_named, hpeq, hqeq⟩
theorem selectorShape_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) :
    ∃ r : ℝ, 0 < r ∧
      let T := S.witnessClassAt_v3 r
      T.card = 4 ∧
      S.I3 ⊆ T ∧
      ∃ p q : ℝ²,
        p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
        q ∈ ({Z.a2, Z.b2, S.triangle.v1} : Finset ℝ²) ∧
        T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
        T ∩ S.CP.C2 = ({q} : Finset ℝ²) := by
  classical
  rcases S.k4_at_v3 with ⟨r, hr, hcard⟩
  let T : Finset ℝ² := S.witnessClassAt_v3 r
  have hcore := S.coreSelector_v3 hr hcard
  rcases hcore with ⟨hTcard, hI3sub, hC1le, hC2le⟩
  have hTcard' : T.card = 4 := by simpa [T] using hTcard
  have hC1le' : (T ∩ S.CP.C1).card ≤ 1 := by simpa [T] using hC1le
  have hC2le' : (T ∩ S.CP.C2).card ≤ 1 := by simpa [T] using hC2le
  have hv3notT : S.triangle.v3 ∉ T := by
    intro hv3T
    have hv3eq : dist S.triangle.v3 S.triangle.v3 = r := (Finset.mem_filter.mp hv3T).2
    have h0r : (0 : ℝ) = r := by simpa using hv3eq
    nlinarith only [hr, h0r]
  have hI3sub' : S.I3 ⊆ T ∩ S.I3 := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hI3sub hz, hz⟩
  have hTminus_eq_two : (T \ S.I3).card = 2 := by
    have hsplit : (T \ S.I3).card + (T ∩ S.I3).card = T.card := by
      simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I3
    have hI3ge : S.I3.card ≤ (T ∩ S.I3).card := Finset.card_le_card hI3sub'
    have hI3le : (T ∩ S.I3).card ≤ S.I3.card := Finset.card_le_card Finset.inter_subset_right
    have hI3two : S.I3.card = 2 := S.I3_card_eq_two
    omega
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
    · exact False.elim (hv3notT (hxv3 ▸ hxT))
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
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxT, hxC1⟩))
    · have hxC2 : x ∈ S.CP.C2 := by
        by_cases hxC2 : x ∈ S.CP.C2
        · exact hxC2
        · have : (0 : ℕ) = 1 := by
            simpa [hxC1, hxC2, hxnotC3] using hone
          omega
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hxT, hxC2⟩))
  have hUnion_eq_two :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card = 2 := by
    have hTminus_le : (T \ S.I3).card ≤ ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card :=
      Finset.card_le_card hcover
    have hUnion_le :
        ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card ≤ 2 := by
      calc
        ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card
            ≤ (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card := Finset.card_union_le _ _
        _ ≤ 1 + 1 := by omega
        _ = 2 := by norm_num
    omega
  have hsum_eq_two : (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card = 2 := by
    have hUnion_le_sum : ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card ≤
        (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card := Finset.card_union_le _ _
    omega
  have hC1eq1 : (T ∩ S.CP.C1).card = 1 := by omega
  have hC2eq1 : (T ∩ S.CP.C2).card = 1 := by omega
  obtain ⟨p, hpeq⟩ := Finset.card_eq_one.mp hC1eq1
  obtain ⟨q, hqeq⟩ := Finset.card_eq_one.mp hC2eq1
  have hpT : p ∈ T := by
    have hpmem : p ∈ ({p} : Finset ℝ²) := by simp
    rw [← hpeq] at hpmem
    exact (Finset.mem_inter.mp hpmem).1
  have hqT : q ∈ T := by
    have hqmem : q ∈ ({q} : Finset ℝ²) := by simp
    rw [← hqeq] at hqmem
    exact (Finset.mem_inter.mp hqmem).1
  have hpC1 : p ∈ S.CP.C1 := by
    have hpmem : p ∈ ({p} : Finset ℝ²) := by simp
    rw [← hpeq] at hpmem
    exact (Finset.mem_inter.mp hpmem).2
  have hqC2 : q ∈ S.CP.C2 := by
    have hqmem : q ∈ ({q} : Finset ℝ²) := by simp
    rw [← hqeq] at hqmem
    exact (Finset.mem_inter.mp hqmem).2
  have hp_ne_v3 : p ≠ S.triangle.v3 := by
    intro h
    exact hv3notT (h ▸ hpT)
  have hq_ne_v3 : q ≠ S.triangle.v3 := by
    intro h
    exact hv3notT (h ▸ hqT)
  have hp_named : p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) := by
    by_cases hpv2 : p = S.triangle.v2
    · simp [hpv2]
    · have hpI1 : p ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hp_ne_v3, Finset.mem_erase.mpr ⟨hpv2, hpC1⟩⟩
      have hpI1' : p ∈ ({Z.a1, Z.b1} : Finset ℝ²) := by
        have : p ∈ S.I1 := hpI1
        rw [Z.hI1] at this
        exact this
      rcases Finset.mem_insert.mp hpI1' with hpa1 | hpb1
      · simp [hpa1]
      · have hpb1' : p = Z.b1 := by simpa using hpb1
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hpb1')))
  have hq_named : q ∈ ({Z.a2, Z.b2, S.triangle.v1} : Finset ℝ²) := by
    by_cases hqv1 : q = S.triangle.v1
    · simp [hqv1]
    · have hqI2 : q ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hqv1, Finset.mem_erase.mpr ⟨hq_ne_v3, hqC2⟩⟩
      have hqI2' : q ∈ ({Z.a2, Z.b2} : Finset ℝ²) := by
        have : q ∈ S.I2 := hqI2
        rw [Z.hI2] at this
        exact this
      rcases Finset.mem_insert.mp hqI2' with hqa2 | hqb2
      · simp [hqa2]
      · have hqb2' : q = Z.b2 := by simpa using hqb2
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hqb2')))
  refine ⟨r, hr, ?_⟩
  dsimp [T]
  exact ⟨hTcard, hI3sub, p, q, hp_named, hq_named, hpeq, hqeq⟩
theorem selectorShape_v2_split
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) :
    ∃ r : ℝ, 0 < r ∧
      let T := S.witnessClassAt_v2 r
      T.card = 4 ∧
      S.I2 ⊆ T ∧
      ((∃ p : ℝ²,
          p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) ∧
          T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
          T ∩ S.CP.C3 = ({S.triangle.v1} : Finset ℝ²)) ∨
       (∃ p : ℝ²,
          p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) ∧
          T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
          T ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
       (∃ p : ℝ²,
          p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) ∧
          T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
          T ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²))) := by
  classical
  rcases S.selectorShape_v2 Z with ⟨r, hr, hshape⟩
  dsimp at hshape
  rcases hshape with ⟨hTcard, hI2sub, p, q, hp, hq, hpeq, hqeq⟩
  rcases Finset.mem_insert.mp hq with hqa3 | hq
  · refine ⟨r, hr, ?_⟩
    dsimp
    exact ⟨hTcard, hI2sub, Or.inr (Or.inl ⟨p, hp, hpeq, by simpa [hqa3] using hqeq⟩)⟩
  rcases Finset.mem_insert.mp hq with hqb3 | hq
  · have hqb3' : q = Z.b3 := by simpa using hqb3
    refine ⟨r, hr, ?_⟩
    dsimp
    exact ⟨hTcard, hI2sub, Or.inr (Or.inr ⟨p, hp, hpeq, by simpa [hqb3'] using hqeq⟩)⟩
  have hqv1 : q = S.triangle.v1 := by simpa using hq
  refine ⟨r, hr, ?_⟩
  dsimp
  exact ⟨hTcard, hI2sub, Or.inl ⟨p, hp, hpeq, by simpa [hqv1] using hqeq⟩⟩
theorem selectorShape_v3_split
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) :
    ∃ r : ℝ, 0 < r ∧
      let T := S.witnessClassAt_v3 r
      T.card = 4 ∧
      S.I3 ⊆ T ∧
      ((∃ p : ℝ²,
          p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
          T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
          T ∩ S.CP.C2 = ({S.triangle.v1} : Finset ℝ²)) ∨
       (∃ p : ℝ²,
          p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
          T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
          T ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²)) ∨
       (∃ p : ℝ²,
          p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
          T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
          T ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²))) := by
  classical
  rcases S.selectorShape_v3 Z with ⟨r, hr, hshape⟩
  dsimp at hshape
  rcases hshape with ⟨hTcard, hI3sub, p, q, hp, hq, hpeq, hqeq⟩
  rcases Finset.mem_insert.mp hq with hqa2 | hq
  · refine ⟨r, hr, ?_⟩
    dsimp
    exact ⟨hTcard, hI3sub, Or.inr (Or.inl ⟨p, hp, hpeq, by simpa [hqa2] using hqeq⟩)⟩
  rcases Finset.mem_insert.mp hq with hqb2 | hq
  · have hqb2' : q = Z.b2 := by simpa using hqb2
    refine ⟨r, hr, ?_⟩
    dsimp
    exact ⟨hTcard, hI3sub, Or.inr (Or.inr ⟨p, hp, hpeq, by simpa [hqb2'] using hqeq⟩)⟩
  have hqv1 : q = S.triangle.v1 := by simpa using hq
  refine ⟨r, hr, ?_⟩
  dsimp
  exact ⟨hTcard, hI3sub, Or.inl ⟨p, hp, hpeq, by simpa [hqv1] using hqeq⟩⟩
theorem I1_v3_distance_chain
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    ∃ near far : ℝ²,
      ({near, far} : Finset ℝ²) = S.I1 ∧
      dist S.triangle.v3 near < dist S.triangle.v3 far ∧
      dist S.triangle.v3 far < dist S.triangle.v3 S.triangle.v2 := by
  classical
  have hC1four : S.CP.C1.card = 4 := (S.n5_forced_m44).1
  rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
      (A := A) (C := S.CP.C1) (M := S.triangle)
      S.hconv S.hnoncol S.CP.C1_subset
      (fun x hxA => (S.CP.arc_membership x hxA).1)
      S.CP.v2_mem_C1 S.CP.v3_mem_C1 S.Packet S.Packet.inner_at_v1 with
    ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
  have hm4 : m = 4 := by
    calc
      m = (Finset.univ.image L.points).card := by
        symm
        simpa using Finset.card_image_of_injective (s := Finset.univ) (f := L.points) L.injective
      _ = S.CP.C1.card := by rw [hLC]
      _ = 4 := hC1four
  subst m
  let i0 : Fin 4 := ⟨0, by decide⟩
  let i1 : Fin 4 := ⟨1, by decide⟩
  let i2 : Fin 4 := ⟨2, by decide⟩
  let i3 : Fin 4 := ⟨3, by decide⟩
  have hi12 : i1 < i2 := by decide
  have hi23 : i2 < i3 := by decide
  have hidx0 : (Problem97.CGN.firstIndex Packet.hm : Fin 4) = i0 := by
    ext
    simp [Problem97.CGN.firstIndex, i0]
  have hidx3 : (Problem97.CGN.lastIndex Packet.hm : Fin 4) = i3 := by
    ext
    simp [Problem97.CGN.lastIndex, i3]
  rcases hEnds with hFirstLast | hLastFirst
  · have hmono :
        Problem97.FiniteEndpoint.E3L20b_rightEndpoint_capDistance_strict
          (L.points (Problem97.CGN.lastIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev L) := by
      intro i j hij
      exact Problem97.FiniteEndpoint.E3L20b_of_cgnCapData Packet Hside Hord hij
    have hfirst0 : L.points i0 = S.triangle.v2 := by
      simpa [hidx0, i0] using hFirstLast.1
    have hlast3 : L.points i3 = S.triangle.v3 := by
      simpa [hidx3, i3] using hFirstLast.2
    have hi1rev : i1.rev = i2 := by decide
    have hi2rev : i2.rev = i1 := by decide
    have hi3rev : i3.rev = i0 := by decide
    have hnearfar : dist S.triangle.v3 (L.points i2) < dist S.triangle.v3 (L.points i1) := by
      have htmp :
          dist (L.points i3) (L.points i2) < dist (L.points i3) (L.points i1) := by
        simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points, hidx3,
            hi1rev, hi2rev] using hmono hi12
      simpa [hlast3] using htmp
    have hfarv2 : dist S.triangle.v3 (L.points i1) < dist S.triangle.v3 S.triangle.v2 := by
      have htmp :
          dist (L.points i3) (L.points i1) < dist (L.points i3) (L.points i0) := by
        simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points, hidx3,
            hi2rev, hi3rev] using hmono hi23
      simpa [hlast3, hfirst0] using htmp
    have hnearC1 : L.points i2 ∈ S.CP.C1 := by
      rw [← hLC]
      exact Finset.mem_image.mpr ⟨i2, by simp [i2]⟩
    have hfarC1 : L.points i1 ∈ S.CP.C1 := by
      rw [← hLC]
      exact Finset.mem_image.mpr ⟨i1, by simp [i1]⟩
    have hnear_ne_v2 : L.points i2 ≠ S.triangle.v2 := by
      intro h
      have : i2 = i0 := L.injective (by simpa [hfirst0] using h)
      simpa [i0, i2] using this
    have hnear_ne_v3 : L.points i2 ≠ S.triangle.v3 := by
      intro h
      have : i2 = i3 := L.injective (by simpa [hlast3] using h)
      simpa [i2, i3] using this
    have hfar_ne_v2 : L.points i1 ≠ S.triangle.v2 := by
      intro h
      have : i1 = i0 := L.injective (by simpa [hfirst0] using h)
      simpa [i0, i1] using this
    have hfar_ne_v3 : L.points i1 ≠ S.triangle.v3 := by
      intro h
      have : i1 = i3 := L.injective (by simpa [hlast3] using h)
      simpa [i1, i3] using this
    have hnearI1 : L.points i2 ∈ S.I1 := by
      unfold Problem97.FiniteEndpointShell.I1
      exact Finset.mem_erase.mpr ⟨hnear_ne_v3, Finset.mem_erase.mpr ⟨hnear_ne_v2, hnearC1⟩⟩
    have hfarI1 : L.points i1 ∈ S.I1 := by
      unfold Problem97.FiniteEndpointShell.I1
      exact Finset.mem_erase.mpr ⟨hfar_ne_v3, Finset.mem_erase.mpr ⟨hfar_ne_v2, hfarC1⟩⟩
    have hpair_sub : ({L.points i2, L.points i1} : Finset ℝ²) ⊆ S.I1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa [hx] using hnearI1
      · have hx' : x = L.points i1 := by simpa using hx
        simpa [hx'] using hfarI1
    have hpair_card : ({L.points i2, L.points i1} : Finset ℝ²).card = 2 := by
      have hne : L.points i2 ≠ L.points i1 := by
        intro h
        have : i2 = i1 := L.injective h
        simpa [i1, i2] using this
      simp [hne]
    have hI1le : S.I1.card ≤ ({L.points i2, L.points i1} : Finset ℝ²).card := by
      rw [S.I1_card_eq_two, hpair_card]
    refine ⟨L.points i2, L.points i1, ?_, hnearfar, hfarv2⟩
    exact Finset.eq_of_subset_of_card_le hpair_sub hI1le
  · have hmono :
        Problem97.FiniteEndpoint.E3L20a_leftEndpoint_capDistance_strict
          (L.points (Problem97.CGN.firstIndex Packet.hm))
          (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap L) := by
      intro i j hij
      exact Problem97.FiniteEndpoint.E3L20a_of_cgnCapData Packet Hside Hord hij
    have hfirst0 : L.points i0 = S.triangle.v3 := by
      simpa [hidx0, i0] using hLastFirst.1
    have hlast3 : L.points i3 = S.triangle.v2 := by
      simpa [hidx3, i3] using hLastFirst.2
    have hnearfar : dist S.triangle.v3 (L.points i1) < dist S.triangle.v3 (L.points i2) := by
      have htmp :
          dist (L.points i0) (L.points i1) < dist (L.points i0) (L.points i2) := by
        simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points, hidx0] using hmono hi12
      simpa [hfirst0] using htmp
    have hfarv2 : dist S.triangle.v3 (L.points i2) < dist S.triangle.v3 S.triangle.v2 := by
      have htmp :
          dist (L.points i0) (L.points i2) < dist (L.points i0) (L.points i3) := by
        simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points, hidx0, hidx3]
          using hmono hi23
      simpa [hfirst0, hlast3] using htmp
    have hnearC1 : L.points i1 ∈ S.CP.C1 := by
      rw [← hLC]
      exact Finset.mem_image.mpr ⟨i1, by simp [i1]⟩
    have hfarC1 : L.points i2 ∈ S.CP.C1 := by
      rw [← hLC]
      exact Finset.mem_image.mpr ⟨i2, by simp [i2]⟩
    have hnear_ne_v2 : L.points i1 ≠ S.triangle.v2 := by
      intro h
      have : i1 = i3 := L.injective (by simpa [hlast3] using h)
      simpa [i1, i3] using this
    have hnear_ne_v3 : L.points i1 ≠ S.triangle.v3 := by
      intro h
      have : i1 = i0 := L.injective (by simpa [hfirst0] using h)
      simpa [i0, i1] using this
    have hfar_ne_v2 : L.points i2 ≠ S.triangle.v2 := by
      intro h
      have : i2 = i3 := L.injective (by simpa [hlast3] using h)
      simpa [i2, i3] using this
    have hfar_ne_v3 : L.points i2 ≠ S.triangle.v3 := by
      intro h
      have : i2 = i0 := L.injective (by simpa [hfirst0] using h)
      simpa [i0, i2] using this
    have hnearI1 : L.points i1 ∈ S.I1 := by
      unfold Problem97.FiniteEndpointShell.I1
      exact Finset.mem_erase.mpr ⟨hnear_ne_v3, Finset.mem_erase.mpr ⟨hnear_ne_v2, hnearC1⟩⟩
    have hfarI1 : L.points i2 ∈ S.I1 := by
      unfold Problem97.FiniteEndpointShell.I1
      exact Finset.mem_erase.mpr ⟨hfar_ne_v3, Finset.mem_erase.mpr ⟨hfar_ne_v2, hfarC1⟩⟩
    have hpair_sub : ({L.points i1, L.points i2} : Finset ℝ²) ⊆ S.I1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa [hx] using hnearI1
      · have hx' : x = L.points i2 := by simpa using hx
        simpa [hx'] using hfarI1
    have hpair_card : ({L.points i1, L.points i2} : Finset ℝ²).card = 2 := by
      have hne : L.points i1 ≠ L.points i2 := by
        intro h
        have : i1 = i2 := L.injective h
        simpa [i1, i2] using this
      simp [hne]
    have hI1le : S.I1.card ≤ ({L.points i1, L.points i2} : Finset ℝ²).card := by
      rw [S.I1_card_eq_two, hpair_card]
    refine ⟨L.points i1, L.points i2, ?_, hnearfar, hfarv2⟩
    exact Finset.eq_of_subset_of_card_le hpair_sub hI1le
theorem I3_cap_order_chain
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    ∃ near far : ℝ²,
      ({near, far} : Finset ℝ²) = S.I3 ∧
      dist S.triangle.v1 near < dist S.triangle.v1 far ∧
      dist S.triangle.v2 far < dist S.triangle.v2 near := by
  classical
  have hC3four : S.CP.C3.card = 4 := (S.n5_forced_m44).2.2
  rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
      (A := A) (C := S.CP.C3) (M := S.triangle3)
      S.hconv S.hnoncol S.CP.C3_subset
      (fun x hxA => (S.CP.arc_membership x hxA).2.2)
      S.CP.v1_mem_C3 S.CP.v2_mem_C3 S.packet3 S.packet3.inner_at_v1 with
    ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
  have hm4 : m = 4 := by
    calc
      m = (Finset.univ.image L.points).card := by
        symm
        simpa using Finset.card_image_of_injective (s := Finset.univ) (f := L.points) L.injective
      _ = S.CP.C3.card := by rw [hLC]
      _ = 4 := hC3four
  subst m
  let i0 : Fin 4 := ⟨0, by decide⟩
  let i1 : Fin 4 := ⟨1, by decide⟩
  let i2 : Fin 4 := ⟨2, by decide⟩
  let i3 : Fin 4 := ⟨3, by decide⟩
  have hi12 : i1 < i2 := by decide
  have hi23 : i2 < i3 := by decide
  have hidx0 : (Problem97.CGN.firstIndex Packet.hm : Fin 4) = i0 := by
    ext
    simp [Problem97.CGN.firstIndex, i0]
  have hidx3 : (Problem97.CGN.lastIndex Packet.hm : Fin 4) = i3 := by
    ext
    simp [Problem97.CGN.lastIndex, i3]
  have hi1rev : i1.rev = i2 := by decide
  have hi2rev : i2.rev = i1 := by decide
  have hmonoA :
      Problem97.FiniteEndpoint.E3L20a_leftEndpoint_capDistance_strict
        (L.points (Problem97.CGN.firstIndex Packet.hm))
        (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap L) := by
    intro i j hij
    exact Problem97.FiniteEndpoint.E3L20a_of_cgnCapData Packet Hside Hord hij
  have hmonoB :
      Problem97.FiniteEndpoint.E3L20b_rightEndpoint_capDistance_strict
        (L.points (Problem97.CGN.lastIndex Packet.hm))
        (Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev L) := by
    intro i j hij
    exact Problem97.FiniteEndpoint.E3L20b_of_cgnCapData Packet Hside Hord hij
  have hL_i1_C3 : L.points i1 ∈ S.CP.C3 := by
    rw [← hLC]; exact Finset.mem_image.mpr ⟨i1, by simp [i1]⟩
  have hL_i2_C3 : L.points i2 ∈ S.CP.C3 := by
    rw [← hLC]; exact Finset.mem_image.mpr ⟨i2, by simp [i2]⟩
  have hne12 : L.points i1 ≠ L.points i2 := by
    intro h; have : i1 = i2 := L.injective h; simpa [i1, i2] using this
  rcases hEnds with hFirstLast | hLastFirst
  ·
    have hfirst0 : L.points i0 = S.triangle.v1 := by
      simpa [hidx0, i0] using hFirstLast.1
    have hlast3 : L.points i3 = S.triangle.v2 := by
      simpa [hidx3, i3] using hFirstLast.2
    have hv1order : dist S.triangle.v1 (L.points i1) < dist S.triangle.v1 (L.points i2) := by
      have htmp :
          dist (L.points i0) (L.points i1) < dist (L.points i0) (L.points i2) := by
        simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points, hidx0]
          using hmonoA hi12
      simpa [hfirst0] using htmp
    have hv2order : dist S.triangle.v2 (L.points i2) < dist S.triangle.v2 (L.points i1) := by
      have htmp :
          dist (L.points i3) (L.points i2) < dist (L.points i3) (L.points i1) := by
        simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points, hidx3,
            hi1rev, hi2rev] using hmonoB hi12
      simpa [hlast3] using htmp
    have hnear_ne_v1 : L.points i1 ≠ S.triangle.v1 := by
      intro h; have : i1 = i0 := L.injective (by simpa [hfirst0] using h); simpa [i0, i1] using this
    have hnear_ne_v2 : L.points i1 ≠ S.triangle.v2 := by
      intro h; have : i1 = i3 := L.injective (by simpa [hlast3] using h); simpa [i1, i3] using this
    have hfar_ne_v1 : L.points i2 ≠ S.triangle.v1 := by
      intro h; have : i2 = i0 := L.injective (by simpa [hfirst0] using h); simpa [i0, i2] using this
    have hfar_ne_v2 : L.points i2 ≠ S.triangle.v2 := by
      intro h; have : i2 = i3 := L.injective (by simpa [hlast3] using h); simpa [i2, i3] using this
    have hnearI3 : L.points i1 ∈ S.I3 := by
      unfold Problem97.FiniteEndpointShell.I3
      exact Finset.mem_erase.mpr ⟨hnear_ne_v2, Finset.mem_erase.mpr ⟨hnear_ne_v1, hL_i1_C3⟩⟩
    have hfarI3 : L.points i2 ∈ S.I3 := by
      unfold Problem97.FiniteEndpointShell.I3
      exact Finset.mem_erase.mpr ⟨hfar_ne_v2, Finset.mem_erase.mpr ⟨hfar_ne_v1, hL_i2_C3⟩⟩
    have hpair_sub : ({L.points i1, L.points i2} : Finset ℝ²) ⊆ S.I3 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa [hx] using hnearI3
      · have hx' : x = L.points i2 := by simpa using hx
        simpa [hx'] using hfarI3
    have hpair_card : ({L.points i1, L.points i2} : Finset ℝ²).card = 2 := by
      simp [hne12]
    have hI3le : S.I3.card ≤ ({L.points i1, L.points i2} : Finset ℝ²).card := by
      rw [S.I3_card_eq_two, hpair_card]
    refine ⟨L.points i1, L.points i2, ?_, hv1order, hv2order⟩
    exact Finset.eq_of_subset_of_card_le hpair_sub hI3le
  ·
    have hfirst0 : L.points i0 = S.triangle.v2 := by
      simpa [hidx0, i0] using hLastFirst.1
    have hlast3 : L.points i3 = S.triangle.v1 := by
      simpa [hidx3, i3] using hLastFirst.2
    have hv2order : dist S.triangle.v2 (L.points i1) < dist S.triangle.v2 (L.points i2) := by
      have htmp :
          dist (L.points i0) (L.points i1) < dist (L.points i0) (L.points i2) := by
        simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCap_points, hidx0]
          using hmonoA hi12
      simpa [hfirst0] using htmp
    have hv1order : dist S.triangle.v1 (L.points i2) < dist S.triangle.v1 (L.points i1) := by
      have htmp :
          dist (L.points i3) (L.points i2) < dist (L.points i3) (L.points i1) := by
        simpa [Problem97.FiniteEndpoint.OrderedSideChain.ofOrderedCapRev_points, hidx3,
            hi1rev, hi2rev] using hmonoB hi12
      simpa [hlast3] using htmp
    have hnear_ne_v2 : L.points i2 ≠ S.triangle.v2 := by
      intro h; have : i2 = i0 := L.injective (by simpa [hfirst0] using h); simpa [i0, i2] using this
    have hnear_ne_v1 : L.points i2 ≠ S.triangle.v1 := by
      intro h; have : i2 = i3 := L.injective (by simpa [hlast3] using h); simpa [i2, i3] using this
    have hfar_ne_v2 : L.points i1 ≠ S.triangle.v2 := by
      intro h; have : i1 = i0 := L.injective (by simpa [hfirst0] using h); simpa [i0, i1] using this
    have hfar_ne_v1 : L.points i1 ≠ S.triangle.v1 := by
      intro h; have : i1 = i3 := L.injective (by simpa [hlast3] using h); simpa [i1, i3] using this
    have hnearI3 : L.points i2 ∈ S.I3 := by
      unfold Problem97.FiniteEndpointShell.I3
      exact Finset.mem_erase.mpr ⟨hnear_ne_v2, Finset.mem_erase.mpr ⟨hnear_ne_v1, hL_i2_C3⟩⟩
    have hfarI3 : L.points i1 ∈ S.I3 := by
      unfold Problem97.FiniteEndpointShell.I3
      exact Finset.mem_erase.mpr ⟨hfar_ne_v2, Finset.mem_erase.mpr ⟨hfar_ne_v1, hL_i1_C3⟩⟩
    have hpair_sub : ({L.points i2, L.points i1} : Finset ℝ²) ⊆ S.I3 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa [hx] using hnearI3
      · have hx' : x = L.points i1 := by simpa using hx
        simpa [hx'] using hfarI3
    have hpair_card : ({L.points i2, L.points i1} : Finset ℝ²).card = 2 := by
      simp [hne12.symm]
    have hI3le : S.I3.card ≤ ({L.points i2, L.points i1} : Finset ℝ²).card := by
      rw [S.I3_card_eq_two, hpair_card]
    refine ⟨L.points i2, L.points i1, ?_, hv1order, hv2order⟩
    exact Finset.eq_of_subset_of_card_le hpair_sub hI3le
theorem qEqE_capOrder_opposite
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {q qs : ℝ²}
    (hqI3 : q ∈ S.I3) (hqsI3 : qs ∈ S.I3) (hne : q ≠ qs) :
    (dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2)
      * (dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2) < 0 := by
  classical
  obtain ⟨near, far, hset, h1, h2⟩ := S.I3_cap_order_chain
  rw [← hset] at hqI3 hqsI3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqI3 hqsI3
  rcases hqI3 with hq | hq <;> rcases hqsI3 with hqs | hqs <;> subst hq <;> subst hqs
  · exact absurd rfl hne
  ·
    have hA : dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2 < 0 := by
      nlinarith only [h2, (dist_nonneg : (0 : ℝ) ≤ dist S.triangle.v2 q), (dist_nonneg : (0 : ℝ) ≤ dist S.triangle.v2 qs)]
    have hB : 0 < dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2 := by
      nlinarith only [h1, (dist_nonneg : (0 : ℝ) ≤ dist S.triangle.v1 q), (dist_nonneg : (0 : ℝ) ≤ dist S.triangle.v1 qs)]
    exact mul_neg_of_neg_of_pos hA hB
  ·
    have hA : 0 < dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2 := by
      nlinarith only [h2, (dist_nonneg : (0 : ℝ) ≤ dist S.triangle.v2 q), (dist_nonneg : (0 : ℝ) ≤ dist S.triangle.v2 qs)]
    have hB : dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2 < 0 := by
      nlinarith only [h1, (dist_nonneg : (0 : ℝ) ≤ dist S.triangle.v1 q), (dist_nonneg : (0 : ℝ) ≤ dist S.triangle.v1 qs)]
    exact mul_neg_of_pos_of_neg hA hB
  · exact absurd rfl hne
def SelectorV3SplitPacket
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  let T := S.witnessClassAt_v3 r
  T.card = 4 ∧
  S.I3 ⊆ T ∧
  ((∃ p : ℝ²,
      p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
      T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
      T ∩ S.CP.C2 = ({S.triangle.v1} : Finset ℝ²)) ∨
   (∃ p : ℝ²,
      p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
      T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
      T ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²)) ∨
   (∃ p : ℝ²,
      p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
      T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
      T ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²)))
def SelectorV3Pv2Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  let T := S.witnessClassAt_v3 r
  S.I3 ⊆ T ∧
  T ∩ S.CP.C1 = ({S.triangle.v2} : Finset ℝ²) ∧
  ((T ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²)) ∨
   (T ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²)))
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
theorem b3n9m051_secondCoord_pos_of_dist_lt_centerHeight
    {c p : ℝ²}
    (hr : dist c p < c 1)
    (hpneg : p 1 < 0) :
    False := by
  have hcy : 0 < c 1 := by
    exact lt_of_le_of_lt dist_nonneg hr
  have hsquare :
      dist c p ^ 2 = (c 0 - p 0) ^ 2 + (c 1 - p 1) ^ 2 := by
    rw [b3n9m051_dist_sq_eq_coord_sq_add_coord_sq]
  have hygap : c 1 < c 1 - p 1 := by
    linarith
  have hygap_sq : (c 1) ^ 2 < (c 1 - p 1) ^ 2 := by
    have hpos : 0 < c 1 - p 1 := by linarith
    nlinarith only [hpneg, hcy]
  have hlt_sq : (c 1) ^ 2 < dist c p ^ 2 := by
    rw [hsquare]
    nlinarith only [hygap_sq, sq_nonneg (c 0 - p 0)]
  have hdist_nonneg : 0 ≤ dist c p := dist_nonneg
  have hdist_sq_lt : dist c p ^ 2 < (c 1) ^ 2 := by
    nlinarith only [hsquare, hygap_sq, hr, hcy, hdist_nonneg]
  nlinarith only [hsquare, hygap_sq, hdist_sq_lt]
theorem i3_v3_a2_normalized_height_gap_of_delta_normalization
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S)
    (hnorm : S.I3V3A2DeltaNormalization Z) :
    S.I3V3A2NormalizedHeightGap Z := by
  rcases hnorm with ⟨T, tau, δ, hv1, hv2, ha2, hv3, hδlo, hδhi, hbelow⟩
  refine ⟨T, tau, ?_, hbelow⟩
  have htwoδ_lo : Real.pi / 2 ≤ 2 * δ := by
    linarith
  have htwoδ_hi : 2 * δ < 2 * Real.pi / 3 := by
    linarith
  have hsin_lb :
      Real.sqrt 3 / 2 < Real.sin (2 * δ) := by
    have hpi_sub_lo : Real.pi / 3 < Real.pi - 2 * δ := by
      linarith
    have hpi_sub_hi : Real.pi - 2 * δ ≤ Real.pi / 2 := by
      linarith
    have hsin :
        Real.sin (Real.pi / 3) < Real.sin (Real.pi - 2 * δ) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · exact hpi_sub_hi
      · exact hpi_sub_lo
    rw [Real.sin_pi_sub] at hsin
    simpa [Real.sin_pi_div_three] using hsin
  have hcos_nonpos : Real.cos (2 * δ) ≤ 0 := by
    apply Real.cos_nonpos_of_pi_div_two_le_of_le
    · exact htwoδ_lo
    · linarith [Real.pi_pos, hδhi]
  have hdist_sq :
      dist (T S.triangle.v3) (T Z.a2) ^ 2 =
        2 + Real.cos (2 * δ) - Real.sqrt 3 * Real.sin (2 * δ) := by
    have hsqrt3_sq : Real.sqrt 3 ^ 2 = 3 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)
    have hsin_sq_add_cos_sq : Real.sin δ ^ 2 + Real.cos δ ^ 2 = 1 := by
      simpa using Real.sin_sq_add_cos_sq δ
    rw [hv3, ha2, b3n9m051_dist_sq_eq_coord_sq_add_coord_sq]
    simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    rw [Real.sin_two_mul, Real.cos_two_mul]
    nlinarith only [hsqrt3_sq, hsin_sq_add_cos_sq]
  have hsqrt3_sq : Real.sqrt 3 ^ 2 = 3 := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)
  have hsqrt3_pos : 0 < Real.sqrt 3 := by
    positivity
  have hs3mul : 3 / 2 < Real.sqrt 3 * Real.sin (2 * δ) := by
    nlinarith only [hsqrt3_sq, hsin_lb, hsqrt3_pos]
  have hdist_sq_lt_half : dist (T S.triangle.v3) (T Z.a2) ^ 2 < 1 / 2 := by
    rw [hdist_sq]
    linarith [hcos_nonpos, hs3mul]
  have hdist_nonneg : 0 ≤ dist (T S.triangle.v3) (T Z.a2) := dist_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 / 2 := by
    positivity
  have hdist_lt_sqrt3 :
      dist (T S.triangle.v3) (T Z.a2) < Real.sqrt 3 / 2 := by
    have hsqrt_sq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      nlinarith only [hsqrt3_sq]
    set d : ℝ := dist (T S.triangle.v3) (T Z.a2)
    set s : ℝ := Real.sqrt 3 / 2
    have hd : 0 ≤ d := by
      dsimp [d]
      exact hdist_nonneg
    have hs : 0 ≤ s := by
      dsimp [s]
      exact hsqrt_nonneg
    have hdsq : d ^ 2 < s ^ 2 := by
      dsimp [d, s]
      rw [hsqrt_sq]
      linarith [hdist_sq_lt_half]
    by_contra h
    have hsle : s ≤ d := le_of_not_gt h
    have hsq_ge : s ^ 2 ≤ d ^ 2 := by
      gcongr
    linarith
  have hv3_y : (T S.triangle.v3) 1 = Real.sin (2 * δ) := by
    rw [hv3]
    simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
    rw [Real.sin_two_mul]
    ring_nf
  calc
    dist (T S.triangle.v3) (T Z.a2) < Real.sqrt 3 / 2 := hdist_lt_sqrt3
    _ < Real.sin (2 * δ) := hsin_lb
    _ = (T S.triangle.v3) 1 := hv3_y.symm
theorem i3_no_point_on_v3_radius_at_a2_of_normalized_height_gap
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S)
    (hgap : S.I3V3A2NormalizedHeightGap Z) :
    S.I3NoPointOnV3RadiusAtA2 Z := by
  rcases hgap with ⟨T, tau, hradius, hbelow⟩
  intro x hxI3 hEq
  have hEqT :
      dist (T S.triangle.v3) (T x) = dist (T S.triangle.v3) (T Z.a2) := by
    exact (tau.dist_eq_iff S.triangle.v3 x Z.a2).2 hEq
  have hradius' : dist (T S.triangle.v3) (T x) < (T S.triangle.v3) 1 := by
    rw [hEqT]
    exact hradius
  exact b3n9m051_secondCoord_pos_of_dist_lt_centerHeight hradius' (hbelow x hxI3)
theorem i3_on_v3_radius_at_a2_card_le_one_of_no_hit
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S)
    (hnohit : S.I3NoPointOnV3RadiusAtA2 Z) :
    S.I3OnV3RadiusAtA2CardLeOne Z := by
  classical
  unfold I3OnV3RadiusAtA2CardLeOne
  have hfilter_empty :
      S.I3.filter (fun x => dist S.triangle.v3 x = dist S.triangle.v3 Z.a2) = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim ((hnohit x (Finset.mem_filter.mp hx).1) ((Finset.mem_filter.mp hx).2))
    · intro hx
      exact False.elim (by simpa using hx)
  have hfilter_card :
      (S.I3.filter (fun x => dist S.triangle.v3 x = dist S.triangle.v3 Z.a2)).card = 0 := by
    simpa [hfilter_empty]
  omega
theorem selectorShape_v3_q_eq_v1_impossible_of_distance_chain
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r : ℝ}
    (hpacket : SelectorV3Qv1Packet S Z r)
    (hb1a1 : dist S.triangle.v3 Z.b1 < dist S.triangle.v3 Z.a1)
    (ha1v2 : dist S.triangle.v3 Z.a1 < dist S.triangle.v3 S.triangle.v2)
    (hv2v1 : dist S.triangle.v3 S.triangle.v2 < dist S.triangle.v3 S.triangle.v1) :
    False := by
  classical
  let T := S.witnessClassAt_v3 r
  rcases hpacket with ⟨p, hp, hpeq, hqeq⟩
  have hpT : p ∈ T := by
    have hpmem : p ∈ ({p} : Finset ℝ²) := by simp
    rw [← hpeq] at hpmem
    exact (Finset.mem_inter.mp hpmem).1
  have hv1T : S.triangle.v1 ∈ T := by
    have hv1mem : S.triangle.v1 ∈ ({S.triangle.v1} : Finset ℝ²) := by simp
    rw [← hqeq] at hv1mem
    exact (Finset.mem_inter.mp hv1mem).1
  have hpeqd : dist S.triangle.v3 p = dist S.triangle.v3 S.triangle.v1 := by
    exact (Finset.mem_filter.mp hpT).2.trans ((Finset.mem_filter.mp hv1T).2.symm)
  rcases Finset.mem_insert.mp hp with hpa1 | hp
  · subst hpa1
    linarith
  rcases Finset.mem_insert.mp hp with hpb1 | hpv2
  · have hpb1' : p = Z.b1 := by simpa using hpb1
    subst hpb1'
    linarith
  have hpv2' : p = S.triangle.v2 := by simpa using hpv2
  subst hpv2'
  linarith
theorem selectorShape_v3_q_eq_v1_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r : ℝ}
    (hpacket : SelectorV3Qv1Packet S Z r)
    (hv2v1 : dist S.triangle.v3 S.triangle.v2 < dist S.triangle.v3 S.triangle.v1) :
    False := by
  classical
  rcases S.I1_v3_distance_chain with ⟨near, far, hI1eq, hnearfar, hfarv2⟩
  have hI1card : ({Z.a1, Z.b1} : Finset ℝ²).card = 2 := by
    simpa [Z.hI1] using S.I1_card_eq_two
  have hab_ne : Z.a1 ≠ Z.b1 := by
    intro h
    simp [h] at hI1card
  have haI1 : Z.a1 ∈ S.I1 := by
    rw [Z.hI1]
    simp
  have hbI1 : Z.b1 ∈ S.I1 := by
    rw [Z.hI1]
    simp
  rw [← hI1eq] at haI1 hbI1
  rcases Finset.mem_insert.mp haI1 with haNear | haFar
  · have hbFar : Z.b1 = far := by
      rcases Finset.mem_insert.mp hbI1 with hbNear | hbFar
      · exfalso
        exact hab_ne (haNear.trans hbNear.symm)
      · simpa using hbFar
    have hpacket' : SelectorV3Qv1Packet S (Z.b3n9m051_swapI1) r := by
      simpa [SelectorV3Qv1Packet, ZeroDefectCapLayout.b3n9m051_swapI1, Finset.insert_comm] using hpacket
    apply selectorShape_v3_q_eq_v1_impossible_of_distance_chain
      (S := S) (Z := Z.b3n9m051_swapI1) (r := r) hpacket'
    · simpa [ZeroDefectCapLayout.b3n9m051_swapI1, haNear, hbFar] using hnearfar
    · simpa [ZeroDefectCapLayout.b3n9m051_swapI1, hbFar] using hfarv2
    · exact hv2v1
  · have haFar' : Z.a1 = far := by
      simpa using haFar
    have hbNear : Z.b1 = near := by
      rcases Finset.mem_insert.mp hbI1 with hbNear | hbFar
      · simpa using hbNear
      · exfalso
        have hbFar' : Z.b1 = far := by simpa using hbFar
        exact hab_ne (haFar'.trans hbFar'.symm)
    apply selectorShape_v3_q_eq_v1_impossible_of_distance_chain
      (S := S) (Z := Z) (r := r) hpacket
    · simpa [hbNear, haFar'] using hnearfar
    · simpa [haFar'] using hfarv2
    · exact hv2v1
theorem selectorShape_v3_q_eq_a2_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r : ℝ}
    (hpacket : SelectorV3Qa2Packet S Z r)
    (hbound : S.I3OnV3RadiusAtA2CardLeOne Z) :
    False := by
  classical
  let T := S.witnessClassAt_v3 r
  rcases hpacket with ⟨hI3sub, p, hp, hpeq, hqeq⟩
  have ha2T : Z.a2 ∈ T := by
    have ha2mem : Z.a2 ∈ ({Z.a2} : Finset ℝ²) := by simp
    rw [← hqeq] at ha2mem
    exact (Finset.mem_inter.mp ha2mem).1
  have hra2 : dist S.triangle.v3 Z.a2 = r := by
    exact (Finset.mem_filter.mp ha2T).2
  have hsub :
      S.I3 ⊆ S.I3.filter (fun x => dist S.triangle.v3 x = dist S.triangle.v3 Z.a2) := by
    intro x hxI3
    have hxT : x ∈ T := hI3sub hxI3
    have hxr : dist S.triangle.v3 x = r := (Finset.mem_filter.mp hxT).2
    exact Finset.mem_filter.mpr ⟨hxI3, by simpa [hra2] using hxr⟩
  have hfiltered_ge :
      2 ≤ (S.I3.filter (fun x => dist S.triangle.v3 x = dist S.triangle.v3 Z.a2)).card := by
    have hI3two : S.I3.card = 2 := S.I3_card_eq_two
    have hcard_le := Finset.card_le_card hsub
    omega
  omega
set_option maxHeartbeats 2000000 in
theorem C2_same_open_side_of_base_chord_as_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    ∀ y ∈ ({Z.a2, S.triangle.v3} : Finset ℝ²),
      signedArea2 y S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 > 0 := by
  classical
  intro y hy
  rcases Finset.mem_insert.mp hy with hya2 | hyv3
  · subst hya2
    rcases hbranch with ⟨⟨hA2, h_a2eq, h_v2eq⟩, _, _⟩
    let q1 : ℝ² := S.triangle.v1
    let q2 : ℝ² := S.triangle.v2
    let q3 : ℝ² := S.triangle.v3
    let a : ℝ² := Z.a2
    let center : ℝ² := S.Packet.center
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
    have haC2 : a ∈ S.CP.C2 := by
      unfold Problem97.FiniteEndpointShell.I2 at hA2
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).2
    have haA : a ∈ A := S.CP.C2_subset haC2
    have hr_q1q2 : dist q1 q2 = r := by
      simpa [q1, q2] using (Finset.mem_filter.mp hv2T1).2
    have hr_q1a : dist q1 a = r := by
      simpa [q1, a] using (Finset.mem_filter.mp haT1).2
    have hs_q2q1 : dist q2 q1 = s := by
      simpa [q1, q2] using (Finset.mem_filter.mp hv1T2).2
    have hs_q2a : dist q2 a = s := by
      simpa [q2, a] using (Finset.mem_filter.mp haT2).2
    have hs_q2q3 : dist q2 q3 = s := by
      simpa [q2, q3] using (Finset.mem_filter.mp hv3T2).2
    have ha_q1 : dist q1 a = dist q1 q2 := by
      rw [hr_q1a, hr_q1q2]
    have ha_q2 : dist q2 a = dist q1 q2 := by
      rw [hs_q2a, dist_comm q1 q2, hs_q2q1]
    have hq3_q2 : dist q2 q3 = dist q1 q2 := by
      rw [hs_q2q3, dist_comm q1 q2, hs_q2q1]
    have hu : q2 - q1 ≠ 0 := by
      exact sub_ne_zero.mpr S.triangle.v12_ne.symm
    let u : ℝ² := q2 - q1
    let nvec : ℝ² := Problem97.stdOrientation.rightAngleRotation u
    let β := Problem97.stdOrientation.basisRightAngleRotation u hu
    let M : ℝ² := midpoint ℝ q1 q2
    let X : ℝ² → ℝ := fun z => β.repr (z - M) 0
    let Y : ℝ² → ℝ := fun z => β.repr (z - M) 1
    let yc : ℝ := Y center
    have hsum_pt : ∀ z : ℝ², z - M = X z • u + Y z • nvec := by
      intro z
      simpa [β, X, Y, nvec] using (β.sum_repr (z - M)).symm
    have hnorm_nvec : ‖nvec‖ = ‖u‖ := by
      simpa [nvec] using Problem97.stdOrientation.rightAngleRotation.norm_map u
    have hβu : β.repr u = Finsupp.single 0 (1 : ℝ) := by
      simpa [β, nvec] using (β.repr_self 0)
    have horth : inner ℝ u nvec = 0 := by
      simpa [nvec] using Problem97.stdOrientation.inner_rightAngleRotation_self u
    have harea_u_left : ∀ t : ℝ, Problem97.stdOrientation.areaForm u (t • u) = 0 := by
      intro t
      rw [map_smul]
      simp
    have harea_u_right : ∀ t : ℝ,
        Problem97.stdOrientation.areaForm u (t • nvec) = t * ‖u‖ ^ 2 := by
      intro t
      rw [map_smul]
      simp [nvec, Orientation.areaForm_rightAngleRotation_right]
    have hu_sq_pos : 0 < ‖u‖ ^ 2 := by
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
    have hq1mid : q1 - M = (-(1 / 2 : ℝ)) • u := by
      calc
        q1 - M = (1 / 2 : ℝ) • (q1 - q2) := by
          simpa [M] using (left_sub_midpoint ℝ q1 q2)
        _ = (-(1 / 2 : ℝ)) • u := by
          rw [show q1 - q2 = -u by
            dsimp [u]
            abel_nf]
          simp [smul_neg]
    have hq2mid : q2 - M = (1 / 2 : ℝ) • u := by
      simpa [M, u] using (right_sub_midpoint ℝ q1 q2)
    have hX_q1 : X q1 = -(1 / 2 : ℝ) := by
      have h := congrArg (fun v : ℝ² => β.repr v 0) hq1mid
      change X q1 = (β.repr ((-(1 / 2 : ℝ)) • u)) 0 at h
      rw [map_smul, hβu] at h
      simpa using h
    have hY_q1 : Y q1 = 0 := by
      have h := congrArg (fun v : ℝ² => β.repr v 1) hq1mid
      change Y q1 = (β.repr ((-(1 / 2 : ℝ)) • u)) 1 at h
      rw [map_smul, hβu] at h
      simpa using h
    have hpt_minus_q1 : ∀ z : ℝ²,
        z - q1 = (X z + 1 / 2) • u + Y z • nvec := by
      intro z
      calc
        z - q1 = (z - M) - (q1 - M) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
          abel_nf
        _ = (X z • u + Y z • nvec) - ((-(1 / 2 : ℝ)) • u) := by
          rw [hsum_pt z, hq1mid]
        _ = (X z • u + (1 / 2 : ℝ) • u) + Y z • nvec := by
          rw [sub_eq_add_neg, neg_smul]
          abel_nf
        _ = (X z + 1 / 2) • u + Y z • nvec := by
          rw [← add_smul]
    have hpt_minus_q2 : ∀ z : ℝ²,
        z - q2 = (X z - 1 / 2) • u + Y z • nvec := by
      intro z
      calc
        z - q2 = (z - M) - (q2 - M) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
          abel_nf
        _ = (X z • u + Y z • nvec) - ((1 / 2 : ℝ) • u) := by
          rw [hsum_pt z, hq2mid]
        _ = (X z • u + (-(1 / 2 : ℝ)) • u) + Y z • nvec := by
          rw [sub_eq_add_neg, neg_smul]
          abel_nf
        _ = (X z - 1 / 2) • u + Y z • nvec := by
          rw [← add_smul]
          simp [sub_eq_add_neg]
    have hpt_minus_center : ∀ z : ℝ²,
        z - center = X z • u + (Y z - yc) • nvec := by
      intro z
      have hcenter_perp : inner ℝ (center - M) u = 0 := by
        have hdist_eq : dist center q1 = dist center q2 := by
          rw [dist_comm center q1, dist_comm center q2, dist_eq_norm, dist_eq_norm]
          exact S.Packet.moser_on_boundary_1.trans S.Packet.moser_on_boundary_2.symm
        have hperp : center ∈ AffineSubspace.perpBisector q1 q2 := by
          rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
          simpa using hdist_eq
        have h :=
          (AffineSubspace.mem_perpBisector_iff_inner_eq_zero
            (c := center) (p₁ := q1) (p₂ := q2)).mp hperp
        simpa [M] using h
      have hxc_zero : X center = 0 := by
        have hinner : inner ℝ (center - M) u = X center * ‖u‖ ^ 2 := by
          have horth_rev : inner ℝ nvec u = 0 := by simpa [real_inner_comm] using horth
          calc
            inner ℝ (center - M) u = inner ℝ (X center • u + Y center • nvec) u := by
              rw [hsum_pt center]
            _ = inner ℝ (X center • u) u + inner ℝ (Y center • nvec) u := by
              rw [inner_add_left]
            _ = X center * ‖u‖ ^ 2 + Y center * 0 := by
              rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, horth_rev]
              simp
            _ = X center * ‖u‖ ^ 2 := by ring
        have hsqpos : 0 < ‖u‖ ^ 2 := by
          exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
        nlinarith only [hcenter_perp, hinner, hu_sq_pos]
      calc
        z - center = (z - M) - (center - M) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
          abel_nf
        _ = (X z • u + Y z • nvec) - (Y center • nvec) := by
          rw [hsum_pt z, hsum_pt center, hxc_zero, zero_smul, zero_add]
        _ = X z • u + (Y z • nvec + (-Y center) • nvec) := by
          rw [sub_eq_add_neg, neg_smul]
          abel_nf
        _ = X z • u + (Y z - yc) • nvec := by
          rw [← add_smul]
          rfl
    have hdist_sq_coeff :
        ∀ x y : ℝ, ‖x • u + y • nvec‖ ^ 2 = (x ^ 2 + y ^ 2) * ‖u‖ ^ 2 := by
      intro x y
      have horth' : inner ℝ (x • u) (y • nvec) = 0 := by
        rw [inner_smul_left, inner_smul_right, horth]
        ring
      have hnorm :
          ‖x • u + y • nvec‖ ^ 2 = ‖x • u‖ ^ 2 + ‖y • nvec‖ ^ 2 := by
        simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x • u) (y • nvec) horth'
      have hu_part : ‖x • u‖ ^ 2 = x ^ 2 * ‖u‖ ^ 2 := by
        calc
          ‖x • u‖ ^ 2 = (|x| * ‖u‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs]
          _ = |x| ^ 2 * ‖u‖ ^ 2 := by ring
          _ = x ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
      have hn_part : ‖y • nvec‖ ^ 2 = y ^ 2 * ‖u‖ ^ 2 := by
        calc
          ‖y • nvec‖ ^ 2 = (|y| * ‖u‖) ^ 2 := by
            rw [norm_smul, Real.norm_eq_abs, hnorm_nvec]
          _ = |y| ^ 2 * ‖u‖ ^ 2 := by ring
          _ = y ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
      rw [hnorm, hu_part, hn_part]
      ring
    have hdist_center_sq :
        ∀ z : ℝ², dist center z ^ 2 = (X z ^ 2 + (Y z - yc) ^ 2) * ‖u‖ ^ 2 := by
      intro z
      rw [dist_comm, dist_eq_norm, hpt_minus_center, hdist_sq_coeff]
    have hdist_q1_sq :
        ∀ z : ℝ², dist q1 z ^ 2 = ((X z + 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 := by
      intro z
      rw [dist_comm, dist_eq_norm, hpt_minus_q1, hdist_sq_coeff]
    have hdist_q2_sq :
        ∀ z : ℝ², dist q2 z ^ 2 = ((X z - 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 := by
      intro z
      rw [dist_comm, dist_eq_norm, hpt_minus_q2, hdist_sq_coeff]
    have hcommon_coords :
        ∀ z : ℝ²,
          dist q1 z = dist q1 q2 →
          dist q2 z = dist q1 q2 →
          X z = 0 ∧ Y z ^ 2 = (3 : ℝ) / 4 := by
      intro z hz1 hz2
      have hu_sq_ne : ‖u‖ ^ 2 ≠ 0 := ne_of_gt hu_sq_pos
      have h1 : ((X z + 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = ‖u‖ ^ 2 := by
        rw [← hdist_q1_sq z, hz1, dist_eq_norm]
        simpa [u, norm_sub_rev]
      have h2 : ((X z - 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = ‖u‖ ^ 2 := by
        rw [← hdist_q2_sq z, hz2, dist_eq_norm]
        simpa [u, norm_sub_rev]
      have h1' : (X z + 1 / 2) ^ 2 + Y z ^ 2 = 1 := by
        have h1'' : ((X z + 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = 1 * ‖u‖ ^ 2 := by
          simpa using h1
        exact mul_right_cancel₀ hu_sq_ne h1''
      have h2' : (X z - 1 / 2) ^ 2 + Y z ^ 2 = 1 := by
        have h2'' : ((X z - 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = 1 * ‖u‖ ^ 2 := by
          simpa using h2
        exact mul_right_cancel₀ hu_sq_ne h2''
      have hx : X z = 0 := by
        have h1r := h1'
        have h2r := h2'
        ring_nf at h1r h2r
        linarith
      have hy : Y z ^ 2 = (3 : ℝ) / 4 := by
        have h1r := h1'
        rw [hx] at h1r
        norm_num at h1r
        linarith
      exact ⟨hx, hy⟩
    have haXhY := hcommon_coords a ha_q1 ha_q2
    rcases haXhY with ⟨haX, haYsq⟩
    have hyc_pos : 0 < Y a * yc := by
      have hdisk_a' : ‖a - center‖ ≤ S.Packet.radius := by
        simpa [center] using S.Packet.disk_contains_A a haA
      have hdisk_a : dist center a ≤ S.Packet.radius := by
        rw [dist_eq_norm, norm_sub_rev]
        exact hdisk_a'
      have hradius : dist center q1 = S.Packet.radius := by
        rw [dist_comm, dist_eq_norm]
        exact S.Packet.moser_on_boundary_1
      have hdist_sq : dist center a ^ 2 ≤ dist center q1 ^ 2 := by
        have hnonneg_a : 0 ≤ dist center a := dist_nonneg
        have hnonneg_q1 : 0 ≤ dist center q1 := dist_nonneg
        nlinarith only [hdisk_a, hradius, hnonneg_a, hnonneg_q1]
      rw [hdist_center_sq a, hdist_center_sq q1, haX, hX_q1, hY_q1] at hdist_sq
      have hdist_sq' : (Y a - yc) ^ 2 ≤ ((1 / 2 : ℝ) ^ 2) + yc ^ 2 := by
        have htmp :
            (Y a - yc) ^ 2 * ‖u‖ ^ 2 ≤
              (((1 / 2 : ℝ) ^ 2) + yc ^ 2) * ‖u‖ ^ 2 := by
          simpa [pow_two] using hdist_sq
        exact le_of_mul_le_mul_right htmp hu_sq_pos
      have hquarter : ((1 / 2 : ℝ) ^ 2) ≤ Y a * yc := by
        have hsq := hdist_sq'
        ring_nf at hsq
        nlinarith only [haYsq, hdist_sq', hsq]
      linarith
    have harea_q1q2 : ∀ z : ℝ², signedArea2 q1 q2 z = Y z * ‖u‖ ^ 2 := by
      intro z
      calc
        signedArea2 q1 q2 z = Problem97.stdOrientation.areaForm u (z - q1) := by
          rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
        _ = Problem97.stdOrientation.areaForm u ((X z + 1 / 2) • u + Y z • nvec) := by
          rw [hpt_minus_q1]
        _ = Y z * ‖u‖ ^ 2 := by
          rw [map_add, harea_u_left (X z + 1 / 2), harea_u_right (Y z)]
          simp
    have hprod_a_center :
        signedArea2 a q1 q2 * signedArea2 center q1 q2 > 0 := by
      have hcyc_a : signedArea2 a q1 q2 = signedArea2 q1 q2 a := by
        unfold signedArea2
        ring
      have hcyc_c : signedArea2 center q1 q2 = signedArea2 q1 q2 center := by
        unfold signedArea2
        ring
      rw [hcyc_a, hcyc_c, harea_q1q2 a, harea_q1q2 center]
      have hu_sq_sq_pos : 0 < ‖u‖ ^ 2 * ‖u‖ ^ 2 := mul_pos hu_sq_pos hu_sq_pos
      have hrew :
          Y a * ‖u‖ ^ 2 * (Y center * ‖u‖ ^ 2) =
            (Y a * yc) * (‖u‖ ^ 2 * ‖u‖ ^ 2) := by
        dsimp [yc]
        ring
      rw [hrew]
      exact mul_pos hyc_pos hu_sq_sq_pos
    have hq1O : ‖q1 - center‖ = S.Packet.radius := by
      simpa [q1, center] using S.Packet.moser_on_boundary_1
    have hq2O : ‖q2 - center‖ = S.Packet.radius := by
      simpa [q2, center] using S.Packet.moser_on_boundary_2
    have hq3O : ‖q3 - center‖ = S.Packet.radius := by
      simpa [q3, center] using S.Packet.moser_on_boundary_3
    have hinner_v3_pos : 0 < inner ℝ (q1 - q3) (q2 - q3) := by
      have hnn : 0 ≤ inner ℝ (q1 - q3) (q2 - q3) := by
        simpa [q1, q2, q3] using S.Packet.inner_at_v3
      by_contra hnot
      have hzero : inner ℝ (q1 - q3) (q2 - q3) = 0 := by linarith
      have hpyth :
          dist q1 q2 ^ 2 = dist q1 q3 ^ 2 + dist q2 q3 ^ 2 := by
        have hvec : q1 - q2 = (q1 - q3) - (q2 - q3) := by
          dsimp [q1, q2, q3]
          abel_nf
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, hvec, norm_sub_sq_real]
        nlinarith only [hnot, hnn, hzero]
      have hq3q1_sq : dist q1 q3 ^ 2 = 0 := by
        rw [hq3_q2] at hpyth
        nlinarith only [hpyth]
      have hq3q1_zero : dist q1 q3 = 0 := by
        have hnn' : 0 ≤ dist q1 q3 := dist_nonneg
        nlinarith only [hnn', hq3q1_sq]
      exact S.triangle.v13_ne (dist_eq_zero.mp hq3q1_zero)
    have hcenter_q3 :
        signedArea2 center q1 q2 * signedArea2 q3 q1 q2 > 0 := by
      have hmid_pos : 0 < inner ℝ (midpoint ℝ q1 q2 - center) (midpoint ℝ q1 q2 - q3) := by
        have hq1q3 : ‖q1 - center‖ = ‖q3 - center‖ := by rw [hq1O, hq3O]
        have hq2q3 : ‖q2 - center‖ = ‖q3 - center‖ := by rw [hq2O, hq3O]
        have hchord := inner_chord_eq_two_mul_inner_midpoint hq1q3 hq2q3
        nlinarith only [hinner_v3_pos, hchord]
      have hperp : ‖q1 - center‖ ^ 2 = ‖q2 - center‖ ^ 2 := by
        rw [hq1O, hq2O]
      rw [Problem97.signedArea_prod_eq_inner_mul_dist_sq center q1 q2 q3 hperp]
      have hchord_sq_pos : 0 < ‖q1 - q2‖ ^ 2 := by
        exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr S.triangle.v12_ne))
      nlinarith only [hmid_pos, hchord_sq_pos]
    have hcenter_ne :
        signedArea2 center q1 q2 ≠ 0 := by
      have : signedArea2 center q1 q2 * signedArea2 q3 q1 q2 ≠ 0 := by
        exact ne_of_gt hcenter_q3
      exact left_ne_zero_of_mul this
    have hprod_av3 :
        signedArea2 a q1 q2 * signedArea2 q3 q1 q2 > 0 := by
      have hcombo :
          0 < (signedArea2 a q1 q2 * signedArea2 center q1 q2) *
            (signedArea2 center q1 q2 * signedArea2 q3 q1 q2) := by
        exact mul_pos hprod_a_center hcenter_q3
      have hrew :
          (signedArea2 a q1 q2 * signedArea2 center q1 q2) *
              (signedArea2 center q1 q2 * signedArea2 q3 q1 q2) =
            (signedArea2 a q1 q2 * signedArea2 q3 q1 q2) *
              (signedArea2 center q1 q2) ^ 2 := by
        ring
      rw [hrew] at hcombo
      have hcenter_sq_pos : 0 < (signedArea2 center q1 q2) ^ 2 := by
        exact sq_pos_of_ne_zero hcenter_ne
      nlinarith only [hcombo, hcenter_sq_pos]
    simpa [a, q1, q2, q3] using hprod_av3
  · have hyv3' : y = S.triangle.v3 := by simpa using hyv3
    subst y
    have hnd :
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 ≠ 0 := by
      have hv1O : ‖S.triangle.v1 - S.Packet.center‖ = S.Packet.radius :=
        S.Packet.moser_on_boundary_1
      have hv2O : ‖S.triangle.v2 - S.Packet.center‖ = S.Packet.radius :=
        S.Packet.moser_on_boundary_2
      have hv3O : ‖S.triangle.v3 - S.Packet.center‖ = S.Packet.radius :=
        S.Packet.moser_on_boundary_3
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        (by simpa [dist_eq_norm] using hv3O)
        (by simpa [dist_eq_norm] using hv1O)
        (by simpa [dist_eq_norm] using hv2O)
        S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
    have hsqpos :
        0 < signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 *
          signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 := by
      exact mul_self_pos.mpr hnd
    simpa [mul_comm] using hsqpos
theorem b3n9m051_c2_sameSide_core (p q s t c : ℝ)
    (hCT : 0 ≤ c * t)
    (hARC : t * (2 * p * t - 2 * q * s - q + t) < 0)
    (hD : p ^ 2 + q ^ 2 ≤ 1 / 4 + 2 * c * q)
    (hC : 8 * c * t = 4 * s ^ 2 + 4 * t ^ 2 - 1) :
    0 < q * t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hc : c ≤ 0 := by nlinarith only [hCT, ht]
    have hARC' : 0 < 2 * p * t - 2 * q * s - q + t := by
      by_contra h; push_neg at h
      nlinarith only [hARC, h, ht, mul_nonpos_of_nonpos_of_nonneg (by linarith : (2 * p * t - 2 * q * s - q + t) ≤ 0) (by linarith : (0 : ℝ) ≤ -t)]
    by_contra hcon; push_neg at hcon
    have hcon' : 0 ≤ q := by nlinarith only [hcon, ht]
    nlinarith only [hARC, hC, hcon, hD, hARC', hcon', ht, hc, mul_nonneg (neg_nonneg.mpr ht.le) (neg_nonneg.mpr hc), sq_nonneg (p - s), mul_nonneg hcon' (neg_nonneg.mpr ht.le), mul_nonneg hcon' (neg_nonneg.mpr hc), sq_nonneg (p * t - q * s), sq_nonneg (q - c), sq_nonneg p, sq_nonneg q]
  · exfalso; rw [ht] at hARC; simp at hARC
  · have hc : 0 ≤ c := by nlinarith only [hCT, ht]
    have hARC' : 2 * p * t - 2 * q * s - q + t < 0 := by
      by_contra h; push_neg at h
      nlinarith only [hARC, h, ht, mul_nonneg h (le_of_lt ht)]
    by_contra hcon; push_neg at hcon
    have hcon' : q ≤ 0 := by nlinarith only [hcon, ht]
    nlinarith only [hARC, hC, hcon, hD, hARC', hcon', ht, hc, mul_nonneg ht.le hc, sq_nonneg (p - s), mul_nonneg (neg_nonneg.mpr hcon') (le_of_lt ht), mul_nonneg (neg_nonneg.mpr hcon') hc, sq_nonneg (p * t - q * s), sq_nonneg (q - c), sq_nonneg p, sq_nonneg q]
set_option maxHeartbeats 4000000 in
theorem c2_vertex_same_open_side_as_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {a₂ : ℝ²}
    (ha2 : a₂ ∈ S.I2) :
    0 < signedArea2 a₂ S.triangle.v1 S.triangle.v2 *
      signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 := by
  classical
  let q1 : ℝ² := S.triangle.v1
  let q2 : ℝ² := S.triangle.v2
  let q3 : ℝ² := S.triangle.v3
  let a : ℝ² := a₂
  let center : ℝ² := S.Packet.center
  have haC2 : a ∈ S.CP.C2 :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp ha2).2).2
  have ha_ne_v1 : a ≠ q1 := (Finset.mem_erase.mp ha2).1
  have ha_ne_v3 : a ≠ q3 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha2).2).1
  have haA : a ∈ A := S.CP.C2_subset haC2
  have harc_le :
      signedArea2 a q3 q1 * signedArea2 q2 q3 q1 ≤ 0 := by
    have h := ((S.CP.arc_membership a haA).2.1).mp haC2
    simpa [Problem97.OnArcOpposite, q1, q2, q3, a] using h
  have hav3v1_ne : signedArea2 a q3 q1 ≠ 0 := by
    intro hΔ
    have hcol : Collinear ℝ ({a, q3, q1} : Set ℝ²) :=
      Problem97.collinear_of_signedArea2_eq_zero a q3 q1 hΔ
    have hconv : ConvexIndep A := S.hconv
    have h3A : q3 ∈ A := S.triangle.v3_mem
    have h1A : q1 ∈ A := S.triangle.v1_mem
    rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
    ·
      apply hconv q3 (by exact_mod_cast h3A)
      have hseg : q3 ∈ segment ℝ a q1 := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨by exact_mod_cast haA, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha_ne_v3 h⟩
      · rcases hx with rfl
        exact ⟨by exact_mod_cast h1A, by
          simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v13_ne h⟩
    ·
      apply hconv q1 (by exact_mod_cast h1A)
      have hseg : q1 ∈ segment ℝ q3 a := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨by exact_mod_cast h3A, by
          simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v13_ne h.symm⟩
      · rcases hx with rfl
        exact ⟨by exact_mod_cast haA, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha_ne_v1 h⟩
    ·
      apply hconv a (by exact_mod_cast haA)
      have hseg : a ∈ segment ℝ q1 q3 := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨by exact_mod_cast h1A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha_ne_v1 h.symm⟩
      · rcases hx with rfl
        exact ⟨by exact_mod_cast h3A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha_ne_v3 h.symm⟩
  have hv2v3v1_ne : signedArea2 q2 q3 q1 ≠ 0 := by
    have hv1O : ‖q1 - S.Packet.center‖ = S.Packet.radius := S.Packet.moser_on_boundary_1
    have hv2O : ‖q2 - S.Packet.center‖ = S.Packet.radius := S.Packet.moser_on_boundary_2
    have hv3O : ‖q3 - S.Packet.center‖ = S.Packet.radius := S.Packet.moser_on_boundary_3
    exact MEC.signedArea2_ne_zero_of_three_dist_eq
      (by simpa [dist_eq_norm] using hv2O)
      (by simpa [dist_eq_norm] using hv3O)
      (by simpa [dist_eq_norm] using hv1O)
      S.triangle.v23_ne S.triangle.v13_ne.symm S.triangle.v12_ne.symm
  have harc : signedArea2 a q3 q1 * signedArea2 q2 q3 q1 < 0 :=
    lt_of_le_of_ne harc_le (mul_ne_zero hav3v1_ne hv2v3v1_ne)
  have hu : q2 - q1 ≠ 0 := sub_ne_zero.mpr S.triangle.v12_ne.symm
  let u : ℝ² := q2 - q1
  let nvec : ℝ² := Problem97.stdOrientation.rightAngleRotation u
  let β := Problem97.stdOrientation.basisRightAngleRotation u hu
  let M : ℝ² := midpoint ℝ q1 q2
  let X : ℝ² → ℝ := fun z => β.repr (z - M) 0
  let Y : ℝ² → ℝ := fun z => β.repr (z - M) 1
  let yc : ℝ := Y center
  have hsum_pt : ∀ z : ℝ², z - M = X z • u + Y z • nvec := by
    intro z
    simpa [β, X, Y, nvec] using (β.sum_repr (z - M)).symm
  have hnorm_nvec : ‖nvec‖ = ‖u‖ := by
    simpa [nvec] using Problem97.stdOrientation.rightAngleRotation.norm_map u
  have horth : inner ℝ u nvec = 0 := by
    simpa [nvec] using Problem97.stdOrientation.inner_rightAngleRotation_self u
  have harea_u_left : ∀ r : ℝ, Problem97.stdOrientation.areaForm u (r • u) = 0 := by
    intro r; rw [map_smul]; simp
  have harea_u_right : ∀ r : ℝ,
      Problem97.stdOrientation.areaForm u (r • nvec) = r * ‖u‖ ^ 2 := by
    intro r; rw [map_smul]
    simp [nvec, Orientation.areaForm_rightAngleRotation_right]
  have hu_sq_pos : 0 < ‖u‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
  have hdiff : ∀ z w : ℝ², z - w = (X z - X w) • u + (Y z - Y w) • nvec := by
    intro z w
    have : (z - M) - (w - M) = z - w := by abel
    rw [← this, hsum_pt z, hsum_pt w, sub_smul, sub_smul]; abel
  have hun : Problem97.stdOrientation.areaForm u nvec = ‖u‖ ^ 2 := by
    simpa using harea_u_right 1
  have hnu : Problem97.stdOrientation.areaForm nvec u = -‖u‖ ^ 2 := by
    rw [Problem97.stdOrientation.areaForm_swap, hun]
  have huu : Problem97.stdOrientation.areaForm u u = 0 := by
    simpa using harea_u_left 1
  have hnn : Problem97.stdOrientation.areaForm nvec nvec = 0 := by simp
  have harea_bilin : ∀ xa ya xb yb : ℝ,
      Problem97.stdOrientation.areaForm (xa • u + ya • nvec) (xb • u + yb • nvec)
        = (xa * yb - ya * xb) * ‖u‖ ^ 2 := by
    intro xa ya xb yb
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, huu, hun, hnu, hnn]
    ring
  have harea_gen : ∀ z w x : ℝ²,
      signedArea2 z w x =
        ((X w - X z) * (Y x - Y z) - (Y w - Y z) * (X x - X z)) * ‖u‖ ^ 2 := by
    intro z w x
    rw [Problem97.signedArea2_eq_stdOrientation_areaForm, hdiff w z, hdiff x z,
        harea_bilin]
  have hXc : X center = 0 := by
    have hdist_eq : dist center q1 = dist center q2 := by
      rw [dist_comm center q1, dist_comm center q2, dist_eq_norm, dist_eq_norm]
      exact S.Packet.moser_on_boundary_1.trans S.Packet.moser_on_boundary_2.symm
    have hperp : center ∈ AffineSubspace.perpBisector q1 q2 := by
      rw [AffineSubspace.mem_perpBisector_iff_dist_eq]; simpa using hdist_eq
    have hcenter_perp : inner ℝ (center - M) u = 0 := by
      have h := (AffineSubspace.mem_perpBisector_iff_inner_eq_zero
        (c := center) (p₁ := q1) (p₂ := q2)).mp hperp
      simpa [M] using h
    have horth_rev : inner ℝ nvec u = 0 := by simpa [real_inner_comm] using horth
    have hinner : inner ℝ (center - M) u = X center * ‖u‖ ^ 2 := by
      calc
        inner ℝ (center - M) u
            = inner ℝ (X center • u + Y center • nvec) u := by rw [hsum_pt center]
        _ = X center * ‖u‖ ^ 2 + Y center * 0 := by
              rw [inner_add_left, inner_smul_left, inner_smul_left,
                real_inner_self_eq_norm_sq, horth_rev]; simp
        _ = X center * ‖u‖ ^ 2 := by ring
    rw [hcenter_perp] at hinner
    have hprod : X center * ‖u‖ ^ 2 = 0 := hinner.symm
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · exact absurd h (ne_of_gt hu_sq_pos)
  have hq1mid : q1 - M = (-(1 / 2 : ℝ)) • u := by
    calc
      q1 - M = (1 / 2 : ℝ) • (q1 - q2) := by
        simpa [M] using (left_sub_midpoint ℝ q1 q2)
      _ = (-(1 / 2 : ℝ)) • u := by
        rw [show q1 - q2 = -u by dsimp [u]; abel_nf]; simp [smul_neg]
  have hq2mid : q2 - M = (1 / 2 : ℝ) • u := by
    simpa [M, u] using (right_sub_midpoint ℝ q1 q2)
  have hβu : β.repr u = Finsupp.single 0 (1 : ℝ) := by
    simpa [β, nvec] using (β.repr_self 0)
  have hX_q1 : X q1 = -(1 / 2 : ℝ) := by
    have h := congrArg (fun v : ℝ² => β.repr v 0) hq1mid
    change X q1 = (β.repr ((-(1 / 2 : ℝ)) • u)) 0 at h
    rw [map_smul, hβu] at h; simpa using h
  have hY_q1 : Y q1 = 0 := by
    have h := congrArg (fun v : ℝ² => β.repr v 1) hq1mid
    change Y q1 = (β.repr ((-(1 / 2 : ℝ)) • u)) 1 at h
    rw [map_smul, hβu] at h; simpa using h
  have hX_q2 : X q2 = (1 / 2 : ℝ) := by
    have h := congrArg (fun v : ℝ² => β.repr v 0) hq2mid
    change X q2 = (β.repr ((1 / 2 : ℝ) • u)) 0 at h
    rw [map_smul, hβu] at h; simpa using h
  have hY_q2 : Y q2 = 0 := by
    have h := congrArg (fun v : ℝ² => β.repr v 1) hq2mid
    change Y q2 = (β.repr ((1 / 2 : ℝ) • u)) 1 at h
    rw [map_smul, hβu] at h; simpa using h
  have hpt_minus_center : ∀ z : ℝ²,
      z - center = X z • u + (Y z - yc) • nvec := by
    intro z
    rw [hdiff z center, hXc]; simp [yc]
  have hdist_sq_coeff :
      ∀ x y : ℝ, ‖x • u + y • nvec‖ ^ 2 = (x ^ 2 + y ^ 2) * ‖u‖ ^ 2 := by
    intro x y
    have horth' : inner ℝ (x • u) (y • nvec) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth]; ring
    have hnorm : ‖x • u + y • nvec‖ ^ 2 = ‖x • u‖ ^ 2 + ‖y • nvec‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x • u) (y • nvec) horth'
    have hu_part : ‖x • u‖ ^ 2 = x ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hn_part : ‖y • nvec‖ ^ 2 = y ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hnorm_nvec, mul_pow, sq_abs]
    rw [hnorm, hu_part, hn_part]; ring
  have hdist_center_sq :
      ∀ z : ℝ², dist center z ^ 2 = (X z ^ 2 + (Y z - yc) ^ 2) * ‖u‖ ^ 2 := by
    intro z
    rw [dist_comm, dist_eq_norm, hpt_minus_center, hdist_sq_coeff]
  have hradius_sq : S.Packet.radius ^ 2 = ((1 / 4 : ℝ) + yc ^ 2) * ‖u‖ ^ 2 := by
    have hr : dist center q1 = S.Packet.radius := by
      rw [dist_comm]; simpa [q1, center, dist_eq_norm, triangle, Problem97.MEC.MoserTriangle.toStructural] using S.Packet.moser_on_boundary_1
    have := hdist_center_sq q1
    rw [hr, hX_q1, hY_q1] at this
    rw [this]; ring
  have hC1 : 8 * yc * Y q3 = 4 * (X q3) ^ 2 + 4 * (Y q3) ^ 2 - 1 := by
    have hr : dist center q3 = S.Packet.radius := by
      rw [dist_comm, dist_eq_norm]; exact S.Packet.moser_on_boundary_3
    have h := hdist_center_sq q3
    rw [hr, hradius_sq] at h
    have hcancel : (X q3) ^ 2 + (Y q3 - yc) ^ 2 = (1 / 4 : ℝ) + yc ^ 2 :=
      (mul_right_cancel₀ (ne_of_gt hu_sq_pos) h).symm
    nlinarith only [hcancel]
  have hD : (X a) ^ 2 + (Y a) ^ 2 ≤ 1 / 4 + 2 * yc * Y a := by
    have hdisk_a' : ‖a - center‖ ≤ S.Packet.radius := by
      simpa [center] using S.Packet.disk_contains_A a haA
    have hdisk_a : dist center a ≤ S.Packet.radius := by
      rw [dist_eq_norm, norm_sub_rev]; exact hdisk_a'
    have hsq : dist center a ^ 2 ≤ S.Packet.radius ^ 2 := by
      have h0 : 0 ≤ dist center a := dist_nonneg
      have h1 : 0 ≤ S.Packet.radius := le_of_lt S.Packet.radius_pos
      nlinarith only [hdisk_a, h0, h1]
    rw [hdist_center_sq a, hradius_sq] at hsq
    have hsq' : (X a) ^ 2 + (Y a - yc) ^ 2 ≤ (1 / 4 : ℝ) + yc ^ 2 :=
      le_of_mul_le_mul_right (by linarith [hsq]) hu_sq_pos
    nlinarith only [hsq']
  have hca : signedArea2 center q1 q2 = yc * ‖u‖ ^ 2 := by
    have hyc : Y center = yc := rfl
    rw [harea_gen center q1 q2, hX_q1, hY_q1, hX_q2, hY_q2, hXc, hyc]; ring
  have hc3 : signedArea2 q3 q1 q2 = Y q3 * ‖u‖ ^ 2 := by
    rw [harea_gen q3 q1 q2, hX_q1, hY_q1, hX_q2, hY_q2]; ring
  have hcenter_q3 : 0 ≤ yc * Y q3 := by
    have hq1O : ‖q1 - center‖ = S.Packet.radius := by
      simpa [q1, center] using S.Packet.moser_on_boundary_1
    have hq2O : ‖q2 - center‖ = S.Packet.radius := by
      simpa [q2, center] using S.Packet.moser_on_boundary_2
    have hq3O : ‖q3 - center‖ = S.Packet.radius := by
      simpa [q3, center] using S.Packet.moser_on_boundary_3
    have hinn : inner ℝ (q1 - q3) (q2 - q3) ≥ 0 := by
      simpa [q1, q2, q3] using S.Packet.inner_at_v3
    have hprod :
        signedArea2 center q1 q2 * signedArea2 q3 q1 q2 ≥ 0 :=
      center_same_side_as_apex_of_nonobtuse hq1O hq2O hq3O hinn
    rw [hca, hc3] at hprod
    have hpos : 0 < ‖u‖ ^ 2 * ‖u‖ ^ 2 := mul_pos hu_sq_pos hu_sq_pos
    nlinarith only [hprod, hpos]
  have hARC : Y q3 * (2 * X a * Y q3 - 2 * Y a * X q3 - Y a + Y q3) < 0 := by
    have hf1 : signedArea2 a q3 q1 =
        ((X q3 - X a) * (Y q1 - Y a) - (Y q3 - Y a) * (X q1 - X a)) * ‖u‖ ^ 2 :=
      harea_gen a q3 q1
    have hf2 : signedArea2 q2 q3 q1 =
        ((X q3 - X q2) * (Y q1 - Y q2) - (Y q3 - Y q2) * (X q1 - X q2)) * ‖u‖ ^ 2 :=
      harea_gen q2 q3 q1
    rw [hf1, hf2, hX_q1, hY_q1, hX_q2, hY_q2] at harc
    have hexpand :
        ((X q3 - X a) * (0 - Y a) - (Y q3 - Y a) * (-(1 / 2) - X a)) * ‖u‖ ^ 2 *
          (((X q3 - (1 / 2)) * (0 - 0) - (Y q3 - 0) * (-(1 / 2) - (1 / 2))) * ‖u‖ ^ 2)
        = (Y q3 * (2 * X a * Y q3 - 2 * Y a * X q3 - Y a + Y q3)) *
            ((1 / 2) * (‖u‖ ^ 2 * ‖u‖ ^ 2)) := by ring
    rw [hexpand] at harc
    have hpos : 0 < (1 / 2 : ℝ) * (‖u‖ ^ 2 * ‖u‖ ^ 2) := by positivity
    nlinarith only [harc, hpos]
  have hcore : 0 < Y a * Y q3 :=
    b3n9m051_c2_sameSide_core (X a) (Y a) (X q3) (Y q3) yc hcenter_q3 hARC hD hC1
  have hsa_a : signedArea2 a q1 q2 = Y a * ‖u‖ ^ 2 := by
    rw [harea_gen a q1 q2, hX_q1, hY_q1, hX_q2, hY_q2]; ring
  have hsa_3 : signedArea2 q3 q1 q2 = Y q3 * ‖u‖ ^ 2 := by
    rw [harea_gen q3 q1 q2, hX_q1, hY_q1, hX_q2, hY_q2]; ring
  change 0 < signedArea2 a q1 q2 * signedArea2 q3 q1 q2
  rw [hsa_a, hsa_3]
  have : Y a * ‖u‖ ^ 2 * (Y q3 * ‖u‖ ^ 2) = (Y a * Y q3) * (‖u‖ ^ 2 * ‖u‖ ^ 2) := by ring
  rw [this]
  exact mul_pos hcore (mul_pos hu_sq_pos hu_sq_pos)
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
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit051

/-- The first N4e slice exports every fact required by later branch proofs. -/
theorem solution {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A) :
    Nonempty (Batch3N9.Problem97.FiniteEndpointShell.N4eCoreSupport S) := by
  exact ⟨{
    layout := S.zeroDefectCapLayout
    I1_card_eq_two := S.I1_card_eq_two
    I2_card_eq_two := S.I2_card_eq_two
    I3_card_eq_two := S.I3_card_eq_two
    coreSelector_v1 := S.coreSelector_v1
    coreSelector_v2 := S.coreSelector_v2
    coreSelector_v3 := S.coreSelector_v3
    formB_v1_split := S.formB_v1_split
    selectorShape_v2_split := S.selectorShape_v2_split
    selectorShape_v3_split := S.selectorShape_v3_split
    qEqE_capOrder_opposite := S.qEqE_capOrder_opposite
    dist_sq_eq_coord_sq_add_coord_sq := Batch3N9.Problem97.FiniteEndpointShell.b3n9m051_dist_sq_eq_coord_sq_add_coord_sq
    qEqE_f1_sinusoid := Batch3N9.Problem97.FiniteEndpointShell.b3n9m051_qEqE_f1_sinusoid
    qEqE_f2_sinusoid := Batch3N9.Problem97.FiniteEndpointShell.b3n9m051_qEqE_f2_sinusoid
    qEqE_lowerArc_sameSign := Batch3N9.Problem97.FiniteEndpointShell.qEqE_lowerArc_sameSign
    qEqE_lowerArc_sameSign_flipped_of_c2Side := Batch3N9.Problem97.FiniteEndpointShell.qEqE_lowerArc_sameSign_flipped_of_c2Side
    i3_v3_a2_normalized_height_gap_of_delta_normalization := S.i3_v3_a2_normalized_height_gap_of_delta_normalization
    i3_no_point_on_v3_radius_at_a2_of_normalized_height_gap := S.i3_no_point_on_v3_radius_at_a2_of_normalized_height_gap
    i3_on_v3_radius_at_a2_card_le_one_of_no_hit := S.i3_on_v3_radius_at_a2_card_le_one_of_no_hit
    selectorShape_v3_q_eq_v1_impossible := S.selectorShape_v3_q_eq_v1_impossible
    selectorShape_v3_q_eq_a2_impossible := S.selectorShape_v3_q_eq_a2_impossible
    C2_same_open_side_of_base_chord_as_v3 := S.C2_same_open_side_of_base_chord_as_v3
    c2_vertex_same_open_side_as_v3 := S.c2_vertex_same_open_side_as_v3
    signedArea2_baseChord_vec2 := Batch3N9.Problem97.FiniteEndpointShell.b3n9m051_signedArea2_baseChord_vec2
    exists_base_transportData := Batch3N9.Problem97.FiniteEndpointShell.b3n9m051_exists_base_transportData
  }⟩
