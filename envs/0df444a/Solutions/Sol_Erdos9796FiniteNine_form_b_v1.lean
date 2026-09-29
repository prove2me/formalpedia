-- Prove2me | solution 1 for Erdos9796FiniteNine.form_b_v1
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T03:28:47.648985+00:00
-- url     : https://prove2.me/submissions/03e034b0-3f2c-4371-bf58-a37f96e453a2

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N4dPackets
import Definitions.Def_Erdos9796FiniteNine_N4dFormBBranchSupport
import Theorems.Thm_Erdos9796FiniteNine_n4e_core
import Theorems.Thm_Erdos9796FiniteNine_n4d_formb_branch

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


section Batch3N9Unit051
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell

noncomputable def p2mCoreSupport {A : Finset ℝ²}
    (S : FiniteEndpointShell A) : N4eCoreSupport S :=
  Classical.choice (Erdos9796FiniteNine.n4e_core S)

noncomputable def p2mBranchSupport {A : Finset ℝ²}
    (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S) :
    N4dFormBBranchSupport S Z :=
  Classical.choice (Erdos9796FiniteNine.n4d_formb_branch S Z)


/-- The selector packet used by the retained Form-B tail. -/
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

/-- The p = v₂ rows used by the retained Form-B producer. -/
def SelectorV3Pv2Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  let T := S.witnessClassAt_v3 r
  S.I3 ⊆ T ∧
  T ∩ S.CP.C1 = ({S.triangle.v2} : Finset ℝ²) ∧
  ((T ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²)) ∨
   (T ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²)))

set_option maxHeartbeats 2000000 in
theorem selectorShape_v2_q_eq_v1_forces_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hr : 0 < r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s) :
    S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) := by
  classical
  rcases hbranch with ⟨⟨hA2, h_a2eq, h_v2eq⟩, -, hpacket⟩
  rcases hpacket with ⟨hTcard_packet, hI2sub_packet, p, hp, hpeq, hqeq⟩
  have hforce : S.SharedCirclePointForcesV3 Z r s := by
    intro q hqnamed hqT2 hqT1
    let q1 : ℝ² := S.triangle.v1
    let q2 : ℝ² := S.triangle.v2
    let a : ℝ² := Z.a2
    let center : ℝ² := S.Packet.center
    have hqA : q ∈ A := (Finset.mem_filter.mp hqT1).1
    have haC2 : a ∈ S.CP.C2 := by
      unfold Problem97.FiniteEndpointShell.I2 at hA2
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).2
    have haA : a ∈ A := S.CP.C2_subset haC2
    have haT1 : a ∈ S.witnessClassAt_v1 r := by
      have hamem : a ∈ ({a} : Finset ℝ²) := by simp
      rw [← h_a2eq] at hamem
      exact (Finset.mem_inter.mp hamem).1
    have haT2 : a ∈ S.witnessClassAt_v2 s := by
      exact hI2sub_packet hA2
    have hv2T1 : q2 ∈ S.witnessClassAt_v1 r := by
      have hv2mem : q2 ∈ ({q2} : Finset ℝ²) := by simp [q2]
      rw [← h_v2eq] at hv2mem
      exact (Finset.mem_inter.mp hv2mem).1
    have hv1T2 : q1 ∈ S.witnessClassAt_v2 s := by
      have hv1mem : q1 ∈ ({q1} : Finset ℝ²) := by simp [q1]
      rw [← hqeq] at hv1mem
      exact (Finset.mem_inter.mp hv1mem).1
    have hr_q1q2 : dist q1 q2 = r := by
      simpa [q1, q2] using (Finset.mem_filter.mp hv2T1).2
    have hr_q1a : dist q1 a = r := by
      simpa [q1, a] using (Finset.mem_filter.mp haT1).2
    have hr_q1q : dist q1 q = r := by
      simpa [q1] using (Finset.mem_filter.mp hqT1).2
    have hs_q2q1 : dist q2 q1 = s := by
      simpa [q1, q2] using (Finset.mem_filter.mp hv1T2).2
    have hs_q2a : dist q2 a = s := by
      simpa [q2, a] using (Finset.mem_filter.mp haT2).2
    have hs_q2q : dist q2 q = s := by
      simpa [q2] using (Finset.mem_filter.mp hqT2).2
    have ha_q1 : dist q1 a = dist q1 q2 := by
      rw [hr_q1a, hr_q1q2]
    have ha_q2 : dist q2 a = dist q1 q2 := by
      rw [hs_q2a, dist_comm q1 q2, hs_q2q1]
    have hq_q1 : dist q1 q = dist q1 q2 := by
      rw [hr_q1q, hr_q1q2]
    have hq_q2 : dist q2 q = dist q1 q2 := by
      rw [hs_q2q, dist_comm q1 q2, hs_q2q1]
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
    have hβu0 : β.repr u 0 = 1 := by simp [hβu]
    have horth : inner ℝ u nvec = 0 := by
      simpa [nvec] using Problem97.stdOrientation.inner_rightAngleRotation_self u
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
    have hX_q2 : X q2 = (1 / 2 : ℝ) := by
      have h := congrArg (fun v : ℝ² => β.repr v 0) hq2mid
      change X q2 = (β.repr ((1 / 2 : ℝ) • u)) 0 at h
      rw [map_smul, hβu] at h
      simpa using h
    have hY_q2 : Y q2 = 0 := by
      have h := congrArg (fun v : ℝ² => β.repr v 1) hq2mid
      change Y q2 = (β.repr ((1 / 2 : ℝ) • u)) 1 at h
      rw [map_smul, hβu] at h
      simpa using h
    have hdist_sq_coeff :
        ∀ a b : ℝ, ‖a • u + b • nvec‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u‖ ^ 2 := by
      intro a b
      have horth' : inner ℝ (a • u) (b • nvec) = 0 := by
        rw [inner_smul_left, inner_smul_right, horth]
        ring
      have hnorm :
          ‖a • u + b • nvec‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • nvec‖ ^ 2 := by
        simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • u) (b • nvec) horth'
      have hu_part : ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
        calc
          ‖a • u‖ ^ 2 = (|a| * ‖u‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs]
          _ = |a| ^ 2 * ‖u‖ ^ 2 := by ring
          _ = a ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
      have hn_part : ‖b • nvec‖ ^ 2 = b ^ 2 * ‖u‖ ^ 2 := by
        calc
          ‖b • nvec‖ ^ 2 = (|b| * ‖u‖) ^ 2 := by
            rw [norm_smul, Real.norm_eq_abs, hnorm_nvec]
          _ = |b| ^ 2 * ‖u‖ ^ 2 := by ring
          _ = b ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
      rw [hnorm, hu_part, hn_part]
      ring
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
        nlinarith only [hcenter_perp, hinner, hsqpos]
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
    have hdist_q1_sq :
        ∀ z : ℝ², dist q1 z ^ 2 = ((X z + 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 := by
      intro z
      rw [dist_comm, dist_eq_norm, hpt_minus_q1, hdist_sq_coeff]
    have hdist_q2_sq :
        ∀ z : ℝ², dist q2 z ^ 2 = ((X z - 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 := by
      intro z
      rw [dist_comm, dist_eq_norm, hpt_minus_q2, hdist_sq_coeff]
    have hdist_center_sq :
        ∀ z : ℝ², dist center z ^ 2 = (X z ^ 2 + (Y z - yc) ^ 2) * ‖u‖ ^ 2 := by
      intro z
      rw [dist_comm, dist_eq_norm, hpt_minus_center, hdist_sq_coeff]
    have hu_sq_pos : 0 < ‖u‖ ^ 2 := by
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
    have hcommon_coords :
        ∀ z : ℝ²,
          dist q1 z = dist q1 q2 →
          dist q2 z = dist q1 q2 →
          X z = 0 ∧ Y z ^ 2 = (3 : ℝ) / 4 := by
      intro z hz1 hz2
      have h1 : ((X z + 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = ‖u‖ ^ 2 := by
        rw [← hdist_q1_sq z, hz1, dist_eq_norm]
        simpa [u, norm_sub_rev]
      have h2 : ((X z - 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = ‖u‖ ^ 2 := by
        rw [← hdist_q2_sq z, hz2, dist_eq_norm]
        simpa [u, norm_sub_rev]
      have hx : X z = 0 := by
        nlinarith only [h1, h2, hu_sq_pos]
      have hy : Y z ^ 2 = (3 : ℝ) / 4 := by
        nlinarith only [h1, h2, hu_sq_pos, hx]
      exact ⟨hx, hy⟩
    have haXhY := hcommon_coords a ha_q1 ha_q2
    have hqXhY := hcommon_coords q hq_q1 hq_q2
    rcases haXhY with ⟨haX, haYsq⟩
    rcases hqXhY with ⟨hqX, hqYsq⟩
    have hy_cases : Y q = Y a ∨ Y q = -Y a := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      rw [hqYsq, haYsq]
    rcases Finset.mem_insert.mp hqnamed with hqa1 | hqrest
    · have hq_a1 : q = Z.a1 := by simpa using hqa1
      rcases hy_cases with hsame | hopp
      · have hqa2 : q = a := by
          have hsub : q - M = a - M := by
            calc
              q - M = X q • u + Y q • nvec := by rw [hsum_pt q]
              _ = 0 • u + Y a • nvec := by simpa [hqX, hsame]
              _ = X a • u + Y a • nvec := by simpa [haX]
              _ = a - M := by rw [hsum_pt a]
          have hadd := congrArg (fun t : ℝ² => t + M) hsub
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
        have hqI1 : q ∈ S.I1 := by
          rw [hq_a1, Z.hI1]
          simp
        have ha_not_verts : a ∉ S.triangle.verts := by
          have ha_ne_v1 : a ≠ q1 := by
            unfold Problem97.FiniteEndpointShell.I2 at hA2
            exact (Finset.mem_erase.mp hA2).1
          have ha_ne_v3 : a ≠ S.triangle.v3 := by
            unfold Problem97.FiniteEndpointShell.I2 at hA2
            exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).1
          have ha_ne_v2 : a ≠ q2 := by
            intro h
            have : q2 ∈ S.CP.C2 := by simpa [h] using haC2
            exact S.CP.v2_notin_C2 this
          simp [Problem97.MoserTriangle.verts, q1, q2, ha_ne_v1, ha_ne_v2, ha_ne_v3]
        have hone_a := S.CP.nonmoser_in_one a haA ha_not_verts
        have haI1 : a ∈ S.I1 := by simpa [hqa2] using hqI1
        have haC1 : a ∈ S.CP.C1 := by
          unfold Problem97.FiniteEndpointShell.I1 at haI1
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase haI1)
        have : False := by
          have hone_a' : (2 + if a ∈ S.CP.C3 then 1 else 0) = 1 := by
            simpa [haC1, haC2] using hone_a
          by_cases haC3 : a ∈ S.CP.C3 <;> simp [haC3] at hone_a'
        exact False.elim this
      · have hyc_pos : 0 < Y a * yc := by
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
          nlinarith only [hu_sq_pos, hdist_sq, haYsq]
        have hq_out : dist center q > S.Packet.radius := by
          have hradius : dist center q1 = S.Packet.radius := by
            rw [dist_comm, dist_eq_norm]
            exact S.Packet.moser_on_boundary_1
          have hdist_sq_q :
              dist center q ^ 2 > S.Packet.radius ^ 2 := by
            rw [hdist_center_sq q]
            have hradius_sq :
                S.Packet.radius ^ 2 = ((1 / 2 : ℝ) ^ 2 + yc ^ 2) * ‖u‖ ^ 2 := by
              have hq1sq := hdist_center_sq q1
              rw [hradius, hX_q1, hY_q1] at hq1sq
              nlinarith only [hq1sq]
            rw [hradius_sq]
            have hqY : Y q = -Y a := by
              exact hopp
            rw [hqX, hqY]
            nlinarith only [hu_sq_pos, haYsq, hyc_pos]
          have hrad_nn : 0 ≤ S.Packet.radius := le_of_lt S.Packet.radius_pos
          have hdist_nn : 0 ≤ dist center q := dist_nonneg
          nlinarith only [hdist_sq_q, hrad_nn, hdist_nn]
        have hdisk_q' : ‖q - center‖ ≤ S.Packet.radius := by
          simpa [center] using S.Packet.disk_contains_A q hqA
        have hdisk_q : dist center q ≤ S.Packet.radius := by
          rw [dist_eq_norm, norm_sub_rev]
          exact hdisk_q'
        exact False.elim (not_le_of_gt hq_out hdisk_q)
    rcases Finset.mem_insert.mp hqrest with hqb1 | hqv3
    · have hq_b1 : q = Z.b1 := by simpa using hqb1
      rcases hy_cases with hsame | hopp
      · have hqb2 : q = a := by
          have hsub : q - M = a - M := by
            calc
              q - M = X q • u + Y q • nvec := by rw [hsum_pt q]
              _ = 0 • u + Y a • nvec := by simpa [hqX, hsame]
              _ = X a • u + Y a • nvec := by simpa [haX]
              _ = a - M := by rw [hsum_pt a]
          have hadd := congrArg (fun t : ℝ² => t + M) hsub
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
        have hqI1 : q ∈ S.I1 := by
          rw [hq_b1, Z.hI1]
          simp
        have ha_not_verts : a ∉ S.triangle.verts := by
          have ha_ne_v1 : a ≠ q1 := by
            unfold Problem97.FiniteEndpointShell.I2 at hA2
            exact (Finset.mem_erase.mp hA2).1
          have ha_ne_v3 : a ≠ S.triangle.v3 := by
            unfold Problem97.FiniteEndpointShell.I2 at hA2
            exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).1
          have ha_ne_v2 : a ≠ q2 := by
            intro h
            have : q2 ∈ S.CP.C2 := by simpa [h] using haC2
            exact S.CP.v2_notin_C2 this
          simp [Problem97.MoserTriangle.verts, q1, q2, ha_ne_v1, ha_ne_v2, ha_ne_v3]
        have hone_a := S.CP.nonmoser_in_one a haA ha_not_verts
        have haI1 : a ∈ S.I1 := by simpa [hqb2] using hqI1
        have haC1 : a ∈ S.CP.C1 := by
          unfold Problem97.FiniteEndpointShell.I1 at haI1
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase haI1)
        have : False := by
          have hone_a' : (2 + if a ∈ S.CP.C3 then 1 else 0) = 1 := by
            simpa [haC1, haC2] using hone_a
          by_cases haC3 : a ∈ S.CP.C3 <;> simp [haC3] at hone_a'
        exact False.elim this
      · have hyc_pos : 0 < Y a * yc := by
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
          nlinarith only [hu_sq_pos, hdist_sq, haYsq]
        have hq_out : dist center q > S.Packet.radius := by
          have hradius : dist center q1 = S.Packet.radius := by
            rw [dist_comm, dist_eq_norm]
            exact S.Packet.moser_on_boundary_1
          have hdist_sq_q :
              dist center q ^ 2 > S.Packet.radius ^ 2 := by
            rw [hdist_center_sq q]
            have hradius_sq :
                S.Packet.radius ^ 2 = ((1 / 2 : ℝ) ^ 2 + yc ^ 2) * ‖u‖ ^ 2 := by
              have hq1sq := hdist_center_sq q1
              rw [hradius, hX_q1, hY_q1] at hq1sq
              nlinarith only [hq1sq]
            rw [hqX, hopp, hradius_sq]
            nlinarith only [hu_sq_pos, haYsq, hyc_pos]
          have hrad_nn : 0 ≤ S.Packet.radius := le_of_lt S.Packet.radius_pos
          have hdist_nn : 0 ≤ dist center q := dist_nonneg
          nlinarith only [hdist_sq_q, hrad_nn, hdist_nn]
        have hdisk_q' : ‖q - center‖ ≤ S.Packet.radius := by
          simpa [center] using S.Packet.disk_contains_A q hqA
        have hdisk_q : dist center q ≤ S.Packet.radius := by
          rw [dist_eq_norm, norm_sub_rev]
          exact hdisk_q'
        exact False.elim (not_le_of_gt hq_out hdisk_q)
    simpa using hqv3
  have hcore := (p2mCoreSupport S).coreSelector_v1 hr hcard
  rcases hcore with ⟨-, hI1sub, -, -⟩
  have hpT2 : p ∈ S.witnessClassAt_v2 s := by
    have hpmem : p ∈ ({p} : Finset ℝ²) := by simp
    rw [← hpeq] at hpmem
    exact (Finset.mem_inter.mp hpmem).1
  rcases Finset.mem_insert.mp hp with hpa1 | hp
  · have hpa1' : p = Z.a1 := by simpa using hpa1
    have ha1I1 : Z.a1 ∈ S.I1 := by
      rw [Z.hI1]
      simp
    have ha1T1 : Z.a1 ∈ S.witnessClassAt_v1 r := hI1sub ha1I1
    have hpv3 : p = S.triangle.v3 := hforce p hp hpT2 (by simpa [hpa1'] using ha1T1)
    simpa [hpv3] using hpeq
  rcases Finset.mem_insert.mp hp with hpb1 | hpv3
  · have hpb1' : p = Z.b1 := by simpa using hpb1
    have hb1I1 : Z.b1 ∈ S.I1 := by
      rw [Z.hI1]
      simp
    have hb1T1 : Z.b1 ∈ S.witnessClassAt_v1 r := hI1sub hb1I1
    have hp123 : p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) := by
      simp [hpb1']
    have hpv3 : p = S.triangle.v3 := hforce p hp123 hpT2 (by simpa [hpb1'] using hb1T1)
    simpa [hpv3] using hpeq
  have hpv3' : p = S.triangle.v3 := by simpa using hpv3
  simpa [hpv3'] using hpeq
theorem selectorShape_v2_q_eq_v1_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hr : 0 < r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s) :
    S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
  classical
  let T := S.witnessClassAt_v2 s
  have hC1eq :
      T ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) :=
    S.selectorShape_v2_q_eq_v1_forces_v3 (Z := Z) (r := r) (s := s) hr hcard hbranch
  rcases hbranch with ⟨⟨-, _, _⟩, _, hpacket⟩
  rcases hpacket with ⟨hTcard, hI2sub, _, _, _, hqeq⟩
  have ha2I2 : Z.a2 ∈ S.I2 := by
    rw [Z.hI2]
    simp
  have hb2I2 : Z.b2 ∈ S.I2 := by
    rw [Z.hI2]
    simp
  have ha2T : Z.a2 ∈ T := hI2sub ha2I2
  have hb2T : Z.b2 ∈ T := hI2sub hb2I2
  have hv3T : S.triangle.v3 ∈ T := by
    have hv3mem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    rw [← hC1eq] at hv3mem
    exact (Finset.mem_inter.mp hv3mem).1
  have hv1T : S.triangle.v1 ∈ T := by
    have hv1mem : S.triangle.v1 ∈ ({S.triangle.v1} : Finset ℝ²) := by simp
    rw [← hqeq] at hv1mem
    exact (Finset.mem_inter.mp hv1mem).1
  have ha2_ne_b2 : Z.a2 ≠ Z.b2 := by
    have hI2card : ({Z.a2, Z.b2} : Finset ℝ²).card = 2 := by
      simpa [Z.hI2] using (p2mCoreSupport S).I2_card_eq_two
    intro h
    simp [h] at hI2card
  have ha2_ne_v1 : Z.a2 ≠ S.triangle.v1 := by
    unfold Problem97.FiniteEndpointShell.I2 at ha2I2
    exact (Finset.mem_erase.mp ha2I2).1
  have hb2_ne_v1 : Z.b2 ≠ S.triangle.v1 := by
    unfold Problem97.FiniteEndpointShell.I2 at hb2I2
    exact (Finset.mem_erase.mp hb2I2).1
  have ha2_ne_v3 : Z.a2 ≠ S.triangle.v3 := by
    unfold Problem97.FiniteEndpointShell.I2 at ha2I2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp ha2I2).2).1
  have hb2_ne_v3 : Z.b2 ≠ S.triangle.v3 := by
    unfold Problem97.FiniteEndpointShell.I2 at hb2I2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hb2I2).2).1
  have hUsub :
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) ⊆ T := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha2T
    · exact hb2T
    · exact hv3T
    · exact hv1T
  have hUcard :
      (insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))).card = 4 := by
    simp [ha2_ne_b2, ha2_ne_v1, hb2_ne_v1, ha2_ne_v3, hb2_ne_v3, S.triangle.v13_ne,
      S.triangle.v13_ne.symm]
  have hTle :
      T.card ≤ (insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))).card := by
    rw [hTcard, hUcard]
  exact (Finset.eq_of_subset_of_card_le hUsub hTle).symm
theorem selectorShape_v2_q_eq_v1_exact_packet_of_b2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hr : 0 < r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hbranch : FormBv1B2SelectorV2Qv1Packet S Z r s) :
    S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
  rcases hbranch with ⟨⟨hb2I2, hb2eq, hv2eq⟩, hs, hpacket⟩
  have hbranch' : FormBv1A2SelectorV2Qv1Packet S (Z.swapI2) r s := by
    refine ⟨?_, hs, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [ZeroDefectCapLayout.swapI2] using hb2I2
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hb2eq
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hv2eq
    · simpa [SelectorV2Qv1Packet, ZeroDefectCapLayout.swapI2] using hpacket
  have hswap :=
    S.selectorShape_v2_q_eq_v1_exact_packet (Z := Z.swapI2) (r := r) (s := s) hr hcard hbranch'
  ext x
  simpa [ZeroDefectCapLayout.swapI2, hswap, Finset.mem_insert, Finset.mem_singleton,
    or_left_comm, or_assoc]
theorem v1v3_longer_than_base_of_exact_packet_of_b2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hbranch : FormBv1B2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3 := by
  rcases hbranch with ⟨⟨hb2I2, hb2eq, hv2eq⟩, hs, hpacket⟩
  have hbranch' : FormBv1A2SelectorV2Qv1Packet S (Z.swapI2) r s := by
    refine ⟨?_, hs, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [ZeroDefectCapLayout.swapI2] using hb2I2
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hb2eq
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hv2eq
    · simpa [SelectorV2Qv1Packet, ZeroDefectCapLayout.swapI2] using hpacket
  have hswap :
      S.witnessClassAt_v2 s =
        insert (Z.swapI2).a2
          (insert (Z.swapI2).b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
    ext x
    simpa [ZeroDefectCapLayout.swapI2, hexact, Finset.mem_insert, Finset.mem_singleton,
      or_left_comm, or_assoc]
  simpa [ZeroDefectCapLayout.swapI2] using
    ((p2mBranchSupport S Z.swapI2).v1v3_longer_than_base_of_exact_packet hbranch' hswap)
theorem selectorShape_v3_q_eq_v1_impossible_of_b2_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hbranch : FormBv1B2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)))
    (hpacket3 : SelectorV3Qv1Packet S Z t) :
    False := by
  have hlong := S.v1v3_longer_than_base_of_exact_packet_of_b2 Z hbranch hexact
  have hv3T : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
    have hv3mem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    simpa [hexact] using hv3mem
  have hv1T : S.triangle.v1 ∈ S.witnessClassAt_v2 s := by
    have hv1mem : S.triangle.v1 ∈ ({S.triangle.v1} : Finset ℝ²) := by simp
    simpa [hexact] using hv1mem
  have hv3dist : dist S.triangle.v2 S.triangle.v3 = s := by
    simpa using (Finset.mem_filter.mp hv3T).2
  have hv1dist : dist S.triangle.v2 S.triangle.v1 = s := by
    simpa using (Finset.mem_filter.mp hv1T).2
  have hv2v1 : dist S.triangle.v3 S.triangle.v2 < dist S.triangle.v3 S.triangle.v1 := by
    calc
      dist S.triangle.v3 S.triangle.v2 = dist S.triangle.v2 S.triangle.v3 := by rw [dist_comm]
      _ = dist S.triangle.v2 S.triangle.v1 := by rw [hv3dist, hv1dist]
      _ = dist S.triangle.v1 S.triangle.v2 := by rw [dist_comm]
      _ < dist S.triangle.v1 S.triangle.v3 := hlong
      _ = dist S.triangle.v3 S.triangle.v1 := by rw [dist_comm]
  exact (p2mCoreSupport S).selectorShape_v3_q_eq_v1_impossible Z hpacket3 hv2v1
theorem n4c_forms_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1) :
    S.IsFormA_v1 r ∨ S.IsFormB_v1 r ∨ S.IsFormC_v1 r := by
  classical
  let T : Finset ℝ² := S.witnessClassAt_v1 r
  have hcore := (p2mCoreSupport S).coreSelector_v1 hr hcard
  rcases hcore with ⟨hTcard, hI1sub, hC2le, hC3le⟩
  have hTcard' : T.card = 4 := by simpa [T] using hTcard
  have hC2le' : (T ∩ S.CP.C2).card ≤ 1 := by simpa [T] using hC2le
  have hC3le' : (T ∩ S.CP.C3).card ≤ 1 := by simpa [T] using hC3le
  have hI1two : S.I1.card = 2 := (p2mCoreSupport S).I1_card_eq_two
  have hI1sub' : S.I1 ⊆ T ∩ S.I1 := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hI1sub hz, hz⟩
  have hTminus_eq_two : (T \ S.I1).card = 2 := by
    have hsplit : (T \ S.I1).card + (T ∩ S.I1).card = T.card := by
      simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I1
    have hI1ge : S.I1.card ≤ (T ∩ S.I1).card := Finset.card_le_card hI1sub'
    have hI1le : (T ∩ S.I1).card ≤ S.I1.card := Finset.card_le_card Finset.inter_subset_right
    omega
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
    · have hv1not : S.triangle.v1 ∉ T := by
        intro hv1T
        have hv1eq : dist S.triangle.v1 S.triangle.v1 = r :=
          (Finset.mem_filter.mp hv1T).2
        have h0r : (0 : ℝ) = r := by simpa using hv1eq
        nlinarith only [hr, h0r]
      exact False.elim (hv1not (hxv1 ▸ hxT))
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
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxT, hxC2⟩))
    · have hxC3 : x ∈ S.CP.C3 := by
        by_cases hxC3 : x ∈ S.CP.C3
        · exact hxC3
        · have : (0 : ℕ) = 1 := by
            simpa [hxnotC1, hxC2, hxC3] using hone
          omega
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hxT, hxC3⟩))
  have hUnion_le :
      ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card ≤ 2 := by
    calc
      ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card
          ≤ (T ∩ S.CP.C2).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by omega
      _ = 2 := by norm_num
  have hUnion_eq_two :
      ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card = 2 := by
    have hTminus_le : (T \ S.I1).card ≤ ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card :=
      Finset.card_le_card hcover
    omega
  have hsum_eq_two : (T ∩ S.CP.C2).card + (T ∩ S.CP.C3).card = 2 := by
    have hUnion_le_sum : ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card ≤
        (T ∩ S.CP.C2).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
    omega
  have hC2eq1 : (T ∩ S.CP.C2).card = 1 := by
    omega
  have hC3eq1 : (T ∩ S.CP.C3).card = 1 := by
    omega
  obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hC2eq1
  obtain ⟨y, hyeq⟩ := Finset.card_eq_one.mp hC3eq1
  have hxT : x ∈ T := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).1
  have hyT : y ∈ T := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).1
  have hxC2 : x ∈ S.CP.C2 := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).2
  have hyC3 : y ∈ S.CP.C3 := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).2
  have hv1notT : S.triangle.v1 ∉ T := by
    intro hv1T
    have hv1eq : dist S.triangle.v1 S.triangle.v1 = r := (Finset.mem_filter.mp hv1T).2
    have h0r : (0 : ℝ) = r := by simpa using hv1eq
    nlinarith only [hr, h0r]
  have hx_ne_v1 : x ≠ S.triangle.v1 := by
    intro h
    exact hv1notT (h ▸ hxT)
  have hy_ne_v1 : y ≠ S.triangle.v1 := by
    intro h
    exact hv1notT (h ▸ hyT)
  by_cases hxv3 : x = S.triangle.v3
  · by_cases hyv2 : y = S.triangle.v2
    · have hsubC1 : T ⊆ S.CP.C1 := by
        intro z hz
        by_cases hzI1 : z ∈ S.I1
        · unfold I1 at hzI1
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzI1).2).2
        · have hzout : z ∈ T \ S.I1 := Finset.mem_sdiff.mpr ⟨hz, hzI1⟩
          have hzcover := hcover hzout
          rcases Finset.mem_union.mp hzcover with hzC2 | hzC3
          · have : z = x := by
              rw [hxeq] at hzC2
              simpa using hzC2
            simpa [this, hxv3] using S.CP.v3_mem_C1
          · have : z = y := by
              rw [hyeq] at hzC3
              simpa using hzC3
            simpa [this, hyv2] using S.CP.v2_mem_C1
      exact False.elim (hesc hsubC1)
    · have hyI3 : y ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hyv2, Finset.mem_erase.mpr ⟨hy_ne_v1, hyC3⟩⟩
      exact Or.inr (Or.inr ⟨y, hyI3, by simpa [T, hxv3] using hxeq, by simpa [T] using hyeq⟩)
  · by_cases hyv2 : y = S.triangle.v2
    · have hxI2 : x ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hx_ne_v1, Finset.mem_erase.mpr ⟨hxv3, hxC2⟩⟩
      exact Or.inr (Or.inl ⟨x, hxI2, by simpa [T] using hxeq, by simpa [T, hyv2] using hyeq⟩)
    · have hxI2 : x ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hx_ne_v1, Finset.mem_erase.mpr ⟨hxv3, hxC2⟩⟩
      have hyI3 : y ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hyv2, Finset.mem_erase.mpr ⟨hy_ne_v1, hyC3⟩⟩
      exact Or.inl ⟨x, y, hxI2, hyI3, by simpa [T] using hxeq, by simpa [T] using hyeq⟩
theorem n4c_forms_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
    (hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2) :
    S.IsFormA_v2 r ∨ S.IsFormB_v2 r ∨ S.IsFormC_v2 r := by
  classical
  let T : Finset ℝ² := S.witnessClassAt_v2 r
  have hcore := (p2mCoreSupport S).coreSelector_v2 hr hcard
  rcases hcore with ⟨hTcard, hI2sub, hC1le, hC3le⟩
  have hTcard' : T.card = 4 := by simpa [T] using hTcard
  have hC1le' : (T ∩ S.CP.C1).card ≤ 1 := by simpa [T] using hC1le
  have hC3le' : (T ∩ S.CP.C3).card ≤ 1 := by simpa [T] using hC3le
  have hI2two : S.I2.card = 2 := (p2mCoreSupport S).I2_card_eq_two
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
    · have hv2not : S.triangle.v2 ∉ T := by
        intro hv2T
        have hv2eq : dist S.triangle.v2 S.triangle.v2 = r :=
          (Finset.mem_filter.mp hv2T).2
        have h0r : (0 : ℝ) = r := by simpa using hv2eq
        nlinarith only [hr, h0r]
      exact False.elim (hv2not (hxv2 ▸ hxT))
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
  have hUnion_le :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card ≤ 2 := by
    calc
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card
          ≤ (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by omega
      _ = 2 := by norm_num
  have hUnion_eq_two :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card = 2 := by
    have hTminus_le : (T \ S.I2).card ≤ ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card :=
      Finset.card_le_card hcover
    omega
  have hsum_eq_two : (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card = 2 := by
    have hUnion_le_sum : ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card ≤
        (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
    omega
  have hC1eq1 : (T ∩ S.CP.C1).card = 1 := by omega
  have hC3eq1 : (T ∩ S.CP.C3).card = 1 := by omega
  obtain ⟨y, hyeq⟩ := Finset.card_eq_one.mp hC1eq1
  obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hC3eq1
  have hxT : x ∈ T := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).1
  have hyT : y ∈ T := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).1
  have hxC3 : x ∈ S.CP.C3 := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).2
  have hyC1 : y ∈ S.CP.C1 := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).2
  have hv2notT : S.triangle.v2 ∉ T := by
    intro hv2T
    have hv2eq : dist S.triangle.v2 S.triangle.v2 = r := (Finset.mem_filter.mp hv2T).2
    have h0r : (0 : ℝ) = r := by simpa using hv2eq
    nlinarith only [hr, h0r]
  have hx_ne_v2 : x ≠ S.triangle.v2 := by
    intro h
    exact hv2notT (h ▸ hxT)
  have hy_ne_v2 : y ≠ S.triangle.v2 := by
    intro h
    exact hv2notT (h ▸ hyT)
  by_cases hxv1 : x = S.triangle.v1
  · by_cases hyv3 : y = S.triangle.v3
    · have hsubC2 : T ⊆ S.CP.C2 := by
        intro z hz
        by_cases hzI2 : z ∈ S.I2
        · unfold I2 at hzI2
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzI2).2).2
        · have hzout : z ∈ T \ S.I2 := Finset.mem_sdiff.mpr ⟨hz, hzI2⟩
          have hzcover := hcover hzout
          rcases Finset.mem_union.mp hzcover with hzC1 | hzC3
          · have : z = y := by
              rw [hyeq] at hzC1
              simpa using hzC1
            simpa [this, hyv3] using S.CP.v3_mem_C2
          · have : z = x := by
              rw [hxeq] at hzC3
              simpa using hzC3
            simpa [this, hxv1] using S.CP.v1_mem_C2
      exact False.elim (hesc hsubC2)
    · have hyI1 : y ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hyv3, Finset.mem_erase.mpr ⟨hy_ne_v2, hyC1⟩⟩
      exact Or.inr (Or.inr ⟨y, hyI1, by simpa [T, hxv1] using hxeq, by simpa [T] using hyeq⟩)
  · by_cases hyv3 : y = S.triangle.v3
    · have hxI3 : x ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hx_ne_v2, Finset.mem_erase.mpr ⟨hxv1, hxC3⟩⟩
      exact Or.inr (Or.inl ⟨x, hxI3, by simpa [T] using hxeq, by simpa [T, hyv3] using hyeq⟩)
    · have hxI3 : x ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hx_ne_v2, Finset.mem_erase.mpr ⟨hxv1, hxC3⟩⟩
      have hyI1 : y ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hyv3, Finset.mem_erase.mpr ⟨hy_ne_v2, hyC1⟩⟩
      exact Or.inl ⟨x, y, hxI3, hyI1, by simpa [T] using hxeq, by simpa [T] using hyeq⟩
theorem n4c_forms_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
    (hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3) :
    S.IsFormA_v3 r ∨ S.IsFormB_v3 r ∨ S.IsFormC_v3 r := by
  classical
  let T : Finset ℝ² := S.witnessClassAt_v3 r
  have hcore := (p2mCoreSupport S).coreSelector_v3 hr hcard
  rcases hcore with ⟨hTcard, hI3sub, hC1le, hC2le⟩
  have hTcard' : T.card = 4 := by simpa [T] using hTcard
  have hC1le' : (T ∩ S.CP.C1).card ≤ 1 := by simpa [T] using hC1le
  have hC2le' : (T ∩ S.CP.C2).card ≤ 1 := by simpa [T] using hC2le
  have hI3two : S.I3.card = 2 := (p2mCoreSupport S).I3_card_eq_two
  have hI3sub' : S.I3 ⊆ T ∩ S.I3 := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hI3sub hz, hz⟩
  have hTminus_eq_two : (T \ S.I3).card = 2 := by
    have hsplit : (T \ S.I3).card + (T ∩ S.I3).card = T.card := by
      simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I3
    have hI3ge : S.I3.card ≤ (T ∩ S.I3).card := Finset.card_le_card hI3sub'
    have hI3le : (T ∩ S.I3).card ≤ S.I3.card := Finset.card_le_card Finset.inter_subset_right
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
    · have hv3not : S.triangle.v3 ∉ T := by
        intro hv3T
        have hv3eq : dist S.triangle.v3 S.triangle.v3 = r :=
          (Finset.mem_filter.mp hv3T).2
        have h0r : (0 : ℝ) = r := by simpa using hv3eq
        nlinarith only [hr, h0r]
      exact False.elim (hv3not (hxv3 ▸ hxT))
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
  have hUnion_le :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card ≤ 2 := by
    calc
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card
          ≤ (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by omega
      _ = 2 := by norm_num
  have hUnion_eq_two :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card = 2 := by
    have hTminus_le : (T \ S.I3).card ≤ ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card :=
      Finset.card_le_card hcover
    omega
  have hsum_eq_two : (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card = 2 := by
    have hUnion_le_sum : ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card ≤
        (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card := Finset.card_union_le _ _
    omega
  have hC1eq1 : (T ∩ S.CP.C1).card = 1 := by omega
  have hC2eq1 : (T ∩ S.CP.C2).card = 1 := by omega
  obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hC1eq1
  obtain ⟨y, hyeq⟩ := Finset.card_eq_one.mp hC2eq1
  have hxT : x ∈ T := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).1
  have hyT : y ∈ T := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).1
  have hxC1 : x ∈ S.CP.C1 := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).2
  have hyC2 : y ∈ S.CP.C2 := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).2
  have hv3notT : S.triangle.v3 ∉ T := by
    intro hv3T
    have hv3eq : dist S.triangle.v3 S.triangle.v3 = r := (Finset.mem_filter.mp hv3T).2
    have h0r : (0 : ℝ) = r := by simpa using hv3eq
    nlinarith only [hr, h0r]
  have hx_ne_v3 : x ≠ S.triangle.v3 := by
    intro h
    exact hv3notT (h ▸ hxT)
  have hy_ne_v3 : y ≠ S.triangle.v3 := by
    intro h
    exact hv3notT (h ▸ hyT)
  by_cases hxv2 : x = S.triangle.v2
  · by_cases hyv1 : y = S.triangle.v1
    · have hsubC3 : T ⊆ S.CP.C3 := by
        intro z hz
        by_cases hzI3 : z ∈ S.I3
        · unfold I3 at hzI3
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzI3).2).2
        · have hzout : z ∈ T \ S.I3 := Finset.mem_sdiff.mpr ⟨hz, hzI3⟩
          have hzcover := hcover hzout
          rcases Finset.mem_union.mp hzcover with hzC1 | hzC2
          · have : z = x := by
              rw [hxeq] at hzC1
              simpa using hzC1
            simpa [this, hxv2] using S.CP.v2_mem_C3
          · have : z = y := by
              rw [hyeq] at hzC2
              simpa using hzC2
            simpa [this, hyv1] using S.CP.v1_mem_C3
      exact False.elim (hesc hsubC3)
    · have hyI2 : y ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hyv1, Finset.mem_erase.mpr ⟨hy_ne_v3, hyC2⟩⟩
      exact Or.inr (Or.inr ⟨y, hyI2, by simpa [T, hxv2] using hxeq, by simpa [T] using hyeq⟩)
  · by_cases hyv1 : y = S.triangle.v1
    · have hxI1 : x ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hx_ne_v3, Finset.mem_erase.mpr ⟨hxv2, hxC1⟩⟩
      exact Or.inr (Or.inl ⟨x, hxI1, by simpa [T] using hxeq, by simpa [T, hyv1] using hyeq⟩)
    · have hxI1 : x ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hx_ne_v3, Finset.mem_erase.mpr ⟨hxv2, hxC1⟩⟩
      have hyI2 : y ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hyv1, Finset.mem_erase.mpr ⟨hy_ne_v3, hyC2⟩⟩
      exact Or.inl ⟨x, y, hxI1, hyI2, by simpa [T] using hxeq, by simpa [T] using hyeq⟩
abbrev N4cClassifies_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Type :=
  ∀ {r : ℝ}, 0 < r →
    4 ≤ (S.witnessClassAt_v1 r).card →
    ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1 →
    EscapedForm
abbrev N4cClassifies_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Type :=
  ∀ {r : ℝ}, 0 < r →
    4 ≤ (S.witnessClassAt_v2 r).card →
    ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2 →
    EscapedForm
abbrev N4cClassifies_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Type :=
  ∀ {r : ℝ}, 0 < r →
    4 ≤ (S.witnessClassAt_v3 r).card →
    ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3 →
    EscapedForm
noncomputable def n4cClassifies_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.N4cClassifies_v1 := by
  classical
  intro r hr hcard hesc
  by_cases hA : S.IsFormA_v1 r
  · exact EscapedForm.a
  · by_cases hB : S.IsFormB_v1 r
    · exact EscapedForm.b
    · have hC : S.IsFormC_v1 r := by
        rcases S.n4c_forms_v1 hr hcard hesc with hA' | hB' | hC'
        · exact False.elim (hA hA')
        · exact False.elim (hB hB')
        · exact hC'
      exact EscapedForm.c
noncomputable def n4cClassifies_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.N4cClassifies_v2 := by
  classical
  intro r hr hcard hesc
  by_cases hA : S.IsFormA_v2 r
  · exact EscapedForm.a
  · by_cases hB : S.IsFormB_v2 r
    · exact EscapedForm.b
    · have hC : S.IsFormC_v2 r := by
        rcases S.n4c_forms_v2 hr hcard hesc with hA' | hB' | hC'
        · exact False.elim (hA hA')
        · exact False.elim (hB hB')
        · exact hC'
      exact EscapedForm.c
noncomputable def n4cClassifies_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.N4cClassifies_v3 := by
  classical
  intro r hr hcard hesc
  by_cases hA : S.IsFormA_v3 r
  · exact EscapedForm.a
  · by_cases hB : S.IsFormB_v3 r
    · exact EscapedForm.b
    · have hC : S.IsFormC_v3 r := by
        rcases S.n4c_forms_v3 hr hcard hesc with hA' | hB' | hC'
        · exact False.elim (hA hA')
        · exact False.elim (hB hB')
        · exact hC'
      exact EscapedForm.c
abbrev N4dExcludes_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (classify : S.N4cClassifies_v1) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
      (hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1),
    False
abbrev N4dExcludes_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (classify : S.N4cClassifies_v2) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
      (hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2),
    False
abbrev N4dExcludes_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (classify : S.N4cClassifies_v3) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
      (hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3),
    False
abbrev b3n9m051_N4dExcludesFormA_v1Pred {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
      (hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1),
    S.IsFormA_v1 r → False
abbrev b3n9m051_N4dExcludesFormB_v1Pred {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
      (hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1),
    S.IsFormB_v1 r → False
abbrev b3n9m051_N4dExcludesFormC_v1Pred {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
      (hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1),
    S.IsFormC_v1 r → False
abbrev b3n9m051_N4dExcludesFormA_v2Pred {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
      (hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2),
    S.IsFormA_v2 r → False
abbrev b3n9m051_N4dExcludesFormB_v2Pred {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
      (hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2),
    S.IsFormB_v2 r → False
abbrev b3n9m051_N4dExcludesFormC_v2Pred {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
      (hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2),
    S.IsFormC_v2 r → False
abbrev b3n9m051_N4dExcludesFormA_v3Pred {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
      (hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3),
    S.IsFormA_v3 r → False
abbrev b3n9m051_N4dExcludesFormB_v3Pred {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
      (hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3),
    S.IsFormB_v3 r → False
abbrev b3n9m051_N4dExcludesFormC_v3Pred {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
      (hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3),
    S.IsFormC_v3 r → False
theorem n4dExcludes_v1_of_forms
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hA : S.N4dExcludesFormA_v1)
    (hB : S.N4dExcludesFormB_v1)
    (hC : S.N4dExcludesFormC_v1) :
    S.N4dExcludes_v1 S.n4cClassifies_v1 := by
  intro r hr hcard hesc
  rcases S.n4c_forms_v1 hr hcard hesc with hform | hform | hform
  · exact hA hr hcard hesc hform
  · exact hB hr hcard hesc hform
  · exact hC hr hcard hesc hform
theorem n4dExcludes_v2_of_forms
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hA : S.N4dExcludesFormA_v2)
    (hB : S.N4dExcludesFormB_v2)
    (hC : S.N4dExcludesFormC_v2) :
    S.N4dExcludes_v2 S.n4cClassifies_v2 := by
  intro r hr hcard hesc
  rcases S.n4c_forms_v2 hr hcard hesc with hform | hform | hform
  · exact hA hr hcard hesc hform
  · exact hB hr hcard hesc hform
  · exact hC hr hcard hesc hform
theorem n4dExcludes_v3_of_forms
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hA : S.N4dExcludesFormA_v3)
    (hB : S.N4dExcludesFormB_v3)
    (hC : S.N4dExcludesFormC_v3) :
    S.N4dExcludes_v3 S.n4cClassifies_v3 := by
  intro r hr hcard hesc
  rcases S.n4c_forms_v3 hr hcard hesc with hform | hform | hform
  · exact hA hr hcard hesc hform
  · exact hB hr hcard hesc hform
  · exact hC hr hcard hesc hform
theorem n4eCapContainment_of_n4c_n4d
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hClass1 : S.N4cClassifies_v1) (hClass2 : S.N4cClassifies_v2)
    (hClass3 : S.N4cClassifies_v3)
    (hExcl1 : S.N4dExcludes_v1 hClass1)
    (hExcl2 : S.N4dExcludes_v2 hClass2)
    (hExcl3 : S.N4dExcludes_v3 hClass3) :
    S.N4eCapContainment := by
  constructor
  · intro r hr hcard
    by_contra hsub
    exact hExcl1 hr hcard hsub
  constructor
  · intro r hr hcard
    by_contra hsub
    exact hExcl2 hr hcard hsub
  · intro r hr hcard
    by_contra hsub
    exact hExcl3 hr hcard hsub
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit051


-- Original module: Solutions.Batch3N9.N4d.BisectorKill
section Batch3N9Unit057
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
theorem b3n9m057_bisectorKill_dist_sq_coords (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 :=
  Problem97.dist_sq_coord x y
theorem b3n9m057_bisectorKill_scalar (bx ox oy px py qx qy xx xy : ℝ)
    (hXperp : (xx - bx) * (px - qx) + xy * (py - qy) = 0)
    (hdperp : (px + qx - 2 * bx) * (px - qx) + (py + qy) * (py - qy) = 0)
    (hPQ : (px - qx) ^ 2 + (py - qy) ^ 2 > 0)
    (hdisk : (xx - ox) ^ 2 + (xy - oy) ^ 2 ≤ (bx - ox) ^ 2 + oy ^ 2)
    (hXy : xy ≤ 0) (hdy : 0 < py + qy)
    (hinner : (px + qx - 2 * bx) * (bx - ox) + (py + qy) * (-oy) < 0)
    (hXne : ¬ (xx = bx ∧ xy = 0)) : False := by
  set dx := px + qx - 2 * bx with hdx
  set dy := py + qy with hdy_def
  set e1 := px - qx with he1
  set e2 := py - qy with he2
  set wx := xx - bx with hwx
  have hcross : (wx * dy - xy * dx) * (e1 ^ 2 + e2 ^ 2) = 0 := by
    have h1 : wx * e1 + xy * e2 = 0 := hXperp
    have h2 : dx * e1 + dy * e2 = 0 := hdperp
    linear_combination (dy * e1 - dx * e2) * h1 + (wx * e2 - xy * e1) * h2
  have hcross' : wx * dy - xy * dx = 0 := by
    rcases mul_eq_zero.mp hcross with h | h
    · exact h
    · exfalso; nlinarith only [hPQ, h]
  have hdy_ne : dy ≠ 0 := ne_of_gt hdy
  set u := xy / dy with hu
  have hxy_eq : xy = u * dy := by rw [hu]; field_simp
  have hwx_eq : wx = u * dx := by
    rw [hu, div_mul_eq_mul_div, eq_div_iff hdy_ne]; linarith [hcross']
  have hu_le : u ≤ 0 := by
    by_contra h; push_neg at h
    have : 0 < u * dy := mul_pos h hdy
    rw [← hxy_eq] at this; linarith [hXy]
  have hu_ne : u ≠ 0 := by
    intro h0; apply hXne
    refine ⟨?_, ?_⟩
    · have : wx = 0 := by rw [hwx_eq, h0]; ring
      simp only [hwx] at this; linarith
    · have : xy = 0 := by rw [hxy_eq, h0]; ring
      linarith
  have hu_lt : u < 0 := lt_of_le_of_ne hu_le hu_ne
  have hxx : xx = bx + u * dx := by
    have := hwx_eq; simp only [hwx] at this; linarith
  have hmargin :
      (xx - ox) ^ 2 + (xy - oy) ^ 2 - ((bx - ox) ^ 2 + oy ^ 2)
        = u * (u * (dx ^ 2 + dy ^ 2) + 2 * (dx * (bx - ox) + dy * (-oy))) := by
    rw [hxx, hxy_eq]; ring
  have hsecond : u * (dx ^ 2 + dy ^ 2) + 2 * (dx * (bx - ox) + dy * (-oy)) < 0 := by
    have h1 : u * (dx ^ 2 + dy ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hu_lt) (by positivity)
    nlinarith only [hinner, h1]
  have hprod : 0 < u * (u * (dx ^ 2 + dy ^ 2) + 2 * (dx * (bx - ox) + dy * (-oy))) :=
    mul_pos_of_neg_of_neg hu_lt hsecond
  linarith [hmargin, hprod, hdisk]
set_option maxHeartbeats 1000000 in
theorem bisectorKill (B O P Q X : ℝ²)
    (hXdisk : dist X O ≤ dist B O)
    (hXeq : dist X P = dist X Q)
    (hBeq : dist B P = dist B Q)
    (hBy0 : B 1 = 0)
    (hXy : X 1 ≤ 0)
    (hdy : 0 < (P 1 - B 1) + (Q 1 - B 1))
    (hinner : ((P 0 - B 0) + (Q 0 - B 0)) * (B 0 - O 0)
       + ((P 1 - B 1) + (Q 1 - B 1)) * (B 1 - O 1) < 0)
    (hPQ : P ≠ Q) (hXne : X ≠ B) : False := by
  have hXsq : dist X P ^ 2 = dist X Q ^ 2 := by rw [hXeq]
  have hBsq : dist B P ^ 2 = dist B Q ^ 2 := by rw [hBeq]
  have hdsq : dist X O ^ 2 ≤ dist B O ^ 2 := pow_le_pow_left₀ dist_nonneg hXdisk 2
  rw [b3n9m057_bisectorKill_dist_sq_coords, b3n9m057_bisectorKill_dist_sq_coords] at hXsq hBsq hdsq
  have hPQne : (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 > 0 := by
    rcases lt_or_eq_of_le
        (show (0 : ℝ) ≤ (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 by positivity) with h | h
    · exact h
    · exfalso; apply hPQ
      ext i; fin_cases i
      · change P 0 = Q 0; nlinarith only [h, sq_nonneg (P 0 - Q 0), sq_nonneg (P 1 - Q 1)]
      · change P 1 = Q 1; nlinarith only [h, sq_nonneg (P 0 - Q 0), sq_nonneg (P 1 - Q 1)]
  have hXneq : ¬ (X 0 = B 0 ∧ X 1 = 0) := by
    rintro ⟨he0, he1⟩; apply hXne
    ext i; fin_cases i
    · exact he0
    · change X 1 = B 1; rw [he1, hBy0]
  rw [hBy0] at hBsq hdsq hdy hinner
  set bx := B 0; clear_value bx
  set ox := O 0; clear_value ox
  set oy := O 1; clear_value oy
  set px := P 0; clear_value px
  set py := P 1; clear_value py
  set qx := Q 0; clear_value qx
  set qy := Q 1; clear_value qy
  set xx := X 0; clear_value xx
  set xy := X 1; clear_value xy
  apply b3n9m057_bisectorKill_scalar bx ox oy px py qx qy xx xy
  · nlinarith only [hBsq, hXsq]
  · nlinarith only [hBsq]
  · exact hPQne
  · nlinarith only [hdsq]
  · exact hXy
  · linarith [hdy]
  · nlinarith only [hinner]
  · exact hXneq
end Problem97
end Batch3N9
end Batch3N9Unit057

-- Original module: Solutions.Batch3N9.N4d.ExcludesFormAv1
section Batch3N9Unit054
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
theorem b3n9m054_hneg_of_cyclicShift_local
    {n : ℕ} {phi : Fin n → ℝ²}
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (cut : Fin n) :
    ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi (i + cut)) (phi (j + cut)) (phi (k + cut)) < 0 := by
  have hcyc {a b c : ℝ²} :
      Problem97.signedArea2 a b c = Problem97.signedArea2 c a b := by
    simp [Problem97.signedArea2]
    ring
  let bound : ℕ := n - cut.val
  have hval_nowrap {t : Fin n} (ht : (t : ℕ) < bound) :
      ((t + cut : Fin n) : ℕ) = t.val + cut.val := by
    rw [Fin.val_add_eq_ite]
    have hlt : ¬ n ≤ t.val + cut.val := by
      omega
    simp [hlt]
  have hval_wrap {t : Fin n} (ht : bound ≤ (t : ℕ)) :
      ((t + cut : Fin n) : ℕ) = t.val - bound := by
    rw [Fin.val_add_eq_ite]
    have hge : n ≤ t.val + cut.val := by
      omega
    simp [hge]
    omega
  intro i j k hij hjk
  by_cases hk : (k : ℕ) < bound
  · have hi : (i : ℕ) < bound := by omega
    have hj : (j : ℕ) < bound := by omega
    have hij' : i + cut < j + cut := by
      change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
      rw [hval_nowrap hi, hval_nowrap hj]
      omega
    have hjk' : j + cut < k + cut := by
      change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
      rw [hval_nowrap hj, hval_nowrap hk]
      omega
    exact hneg hij' hjk'
  · by_cases hj : (j : ℕ) < bound
    · have hi : (i : ℕ) < bound := by omega
      have hk' : bound ≤ (k : ℕ) := by omega
      have hki : k + cut < i + cut := by
        change (((k + cut : Fin n) : ℕ) < ((i + cut : Fin n) : ℕ))
        rw [hval_wrap hk', hval_nowrap hi]
        omega
      have hij' : i + cut < j + cut := by
        change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
        rw [hval_nowrap hi, hval_nowrap hj]
        omega
      have hneg' :
          Problem97.signedArea2 (phi (k + cut)) (phi (i + cut)) (phi (j + cut)) < 0 :=
        hneg hki hij'
      simpa [hcyc] using hneg'
    · by_cases hi : (i : ℕ) < bound
      · have hj' : bound ≤ (j : ℕ) := by omega
        have hk' : bound ≤ (k : ℕ) := by omega
        have hjk'' : j + cut < k + cut := by
          change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
          rw [hval_wrap hj', hval_wrap hk']
          omega
        have hki : k + cut < i + cut := by
          change (((k + cut : Fin n) : ℕ) < ((i + cut : Fin n) : ℕ))
          rw [hval_wrap hk', hval_nowrap hi]
          omega
        have hneg' :
            Problem97.signedArea2 (phi (j + cut)) (phi (k + cut)) (phi (i + cut)) < 0 :=
          hneg hjk'' hki
        simpa [hcyc] using hneg'
      · have hi' : bound ≤ (i : ℕ) := by omega
        have hj' : bound ≤ (j : ℕ) := by omega
        have hk' : bound ≤ (k : ℕ) := by omega
        have hij' : i + cut < j + cut := by
          change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
          rw [hval_wrap hi', hval_wrap hj']
          omega
        have hjk' : j + cut < k + cut := by
          change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
          rw [hval_wrap hj', hval_wrap hk']
          omega
        exact hneg hij' hjk'
theorem b3n9m054_supportCap_interval_of_oppositeFirst_local
    {A C : Finset ℝ²} {n : ℕ} {phi : Fin n → ℝ²}
    {u v w : ℝ²}
    (_hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite u v w x)
    (hv_mem : v ∈ C)
    (hw_mem : w ∈ C)
    {u_idx v_idx w_idx : Fin n}
    (hu : phi u_idx = u)
    (hv : phi v_idx = v)
    (hw : phi w_idx = w)
    (huv : u_idx < v_idx)
    (hvw : v_idx < w_idx) :
    ∀ x : ℝ², x ∈ C ↔ ∃ q : Fin n, v_idx ≤ q ∧ q ≤ w_idx ∧ phi q = x := by
  have hu_neg : Problem97.signedArea2 u v w < 0 := by
    simpa [hu, hv, hw] using hneg huv hvw
  intro x
  constructor
  · intro hxC
    have hxA : x ∈ A := hC_subset hxC
    rw [← hphi_image] at hxA
    rcases Finset.mem_image.mp hxA with ⟨q, _, rfl⟩
    have hqA : phi q ∈ A := by
      rw [← hphi_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
    have hq_arc : Problem97.OnArcOpposite u v w (phi q) :=
      (hC_arc (phi q) hqA).1 hxC
    have hnot_lt_left : ¬ q < v_idx := by
      intro hqv
      have hq_neg : Problem97.signedArea2 (phi q) v w < 0 := by
        simpa [hv, hw] using hneg hqv hvw
      have hprod_pos :
          0 < Problem97.signedArea2 (phi q) v w * Problem97.signedArea2 u v w := by
        have h1 : 0 < -Problem97.signedArea2 (phi q) v w := by linarith
        have h2 : 0 < -Problem97.signedArea2 u v w := by linarith
        have hpos :
            0 < (-Problem97.signedArea2 (phi q) v w) *
              (-Problem97.signedArea2 u v w) := by positivity
        simpa [neg_mul_neg] using hpos
      unfold Problem97.OnArcOpposite at hq_arc
      linarith
    have hnot_lt_right : ¬ w_idx < q := by
      intro hwq
      have hq_neg_vwx : Problem97.signedArea2 v w (phi q) < 0 := by
        simpa [hv, hw] using hneg hvw hwq
      have hcyc : Problem97.signedArea2 (phi q) v w =
          Problem97.signedArea2 v w (phi q) := by
        simp [Problem97.signedArea2]
        ring
      have hq_neg : Problem97.signedArea2 (phi q) v w < 0 := by
        rw [hcyc]
        exact hq_neg_vwx
      have hprod_pos :
          0 < Problem97.signedArea2 (phi q) v w * Problem97.signedArea2 u v w := by
        have h1 : 0 < -Problem97.signedArea2 (phi q) v w := by linarith
        have h2 : 0 < -Problem97.signedArea2 u v w := by linarith
        have hpos :
            0 < (-Problem97.signedArea2 (phi q) v w) *
              (-Problem97.signedArea2 u v w) := by positivity
        simpa [neg_mul_neg] using hpos
      unfold Problem97.OnArcOpposite at hq_arc
      linarith
    exact ⟨q, le_of_not_gt hnot_lt_left, le_of_not_gt hnot_lt_right, rfl⟩
  · rintro ⟨q, hvle, hqle, rfl⟩
    have hqA : phi q ∈ A := by
      rw [← hphi_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
    rcases eq_or_lt_of_le hvle with rfl | hvq
    · simpa [hv] using hv_mem
    rcases eq_or_lt_of_le hqle with rfl | hqw
    · simpa [hw] using hw_mem
    · have hmid_neg : Problem97.signedArea2 v (phi q) w < 0 := by
        simpa [hv, hw] using hneg hvq hqw
      have hcyc : Problem97.signedArea2 (phi q) v w =
          Problem97.signedArea2 v w (phi q) := by
        simp [Problem97.signedArea2]
        ring
      have hswap : Problem97.signedArea2 v w (phi q) =
          -Problem97.signedArea2 v (phi q) w := by
        simp [Problem97.signedArea2]
      have hq_pos : 0 < Problem97.signedArea2 (phi q) v w := by
        rw [hcyc, hswap]
        linarith
      have hq_arc : Problem97.OnArcOpposite u v w (phi q) := by
        unfold Problem97.OnArcOpposite
        have hprod_nonpos :
            Problem97.signedArea2 (phi q) v w * Problem97.signedArea2 u v w ≤ 0 := by
          nlinarith only [hu_neg, hmid_neg, hcyc, hswap]
        exact hprod_nonpos
      exact (hC_arc (phi q) hqA).2 hq_arc
theorem c1_vertex_same_open_side_as_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {p : ℝ²}
    (hpI1 : p ∈ S.I1) :
    0 < signedArea2 p S.triangle.v1 S.triangle.v2 *
      signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 := by
  classical
  have hp_ne_v3 : p ≠ S.triangle.v3 := (Finset.mem_erase.mp hpI1).1
  have hp_ne_v2 : p ≠ S.triangle.v2 :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hpI1).2).1
  have hpC1 : p ∈ S.CP.C1 := by
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hpI1).2).2
  obtain ⟨n, hn, phi, hphi_inj, hphi_image, hccw⟩ :=
    Problem97.CGN.CGN4g0_globalBoundaryOrder_of_convexIndep S.hconv S.hnoncol
  haveI : NeZero n := ⟨by omega⟩
  let i0 : Fin n := 0
  have hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0 := by
    intro i j k hij hjk
    have hij_ne : phi i ≠ phi j := by
      intro h
      exact (ne_of_lt hij) (hphi_inj h)
    have hkj_ne : phi k ≠ phi j := by
      intro h
      exact (ne_of_gt hjk) (hphi_inj h)
    have hswap : Problem97.signedArea2 (phi j) (phi i) (phi k) =
        -Problem97.signedArea2 (phi i) (phi j) (phi k) := by
      simp [Problem97.signedArea2]
      ring
    have hsign :
        SignType.sign (Problem97.signedArea2 (phi j) (phi i) (phi k)) = 1 := by
      rw [Problem97.signedArea2_sign_eq_oangle_sign (phi j) (phi i) (phi k) hij_ne hkj_ne]
      exact hccw.sign_oangle hij hjk
    have hpos : 0 < Problem97.signedArea2 (phi j) (phi i) (phi k) :=
      (sign_eq_one_iff).mp hsign
    linarith
  have hv1A : S.triangle.v1 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact S.triangle.v1_mem
  have hv2A : S.triangle.v2 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact S.triangle.v2_mem
  have hv3A : S.triangle.v3 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact S.triangle.v3_mem
  rcases Finset.mem_image.mp hv1A with ⟨i1, _, hi1⟩
  rcases Finset.mem_image.mp hv2A with ⟨i2, _, hi2⟩
  rcases Finset.mem_image.mp hv3A with ⟨i3, _, hi3⟩
  let psi : Fin n → ℝ² := fun t => phi (t + i1)
  have hpsi_inj : Function.Injective psi := by
    intro a b hab
    apply (finCycle i1).injective
    exact hphi_inj hab
  have hpsi_image : Finset.univ.image psi = A := by
    calc
      Finset.univ.image psi = Finset.univ.image (fun t : Fin n => phi (t + i1)) := rfl
      _ = Finset.univ.image phi := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
          exact Finset.mem_image_of_mem phi (Finset.mem_univ _)
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨q, _, rfl⟩
          refine Finset.mem_image.mpr ?_
          refine ⟨q - i1, Finset.mem_univ _, ?_⟩
          simpa [psi, finCycle] using (Equiv.apply_symm_apply (finCycle i1) q)
      _ = A := hphi_image
  have hneg_shift :
      ∀ {i j k : Fin n}, i < j → j < k →
        Problem97.signedArea2 (psi i) (psi j) (psi k) < 0 := by
    intro i j k hij hjk
    simpa [psi] using
      (b3n9m054_hneg_of_cyclicShift_local (phi := phi) hneg i1 hij hjk :
        Problem97.signedArea2 (phi (i + i1)) (phi (j + i1)) (phi (k + i1)) < 0)
  have hpsi0 : psi i0 = S.triangle.v1 := by
    simpa [psi, i0, hi1]
  have hshift_i2 : (i2 - i1) + i1 = i2 := by
    simpa [finCycle] using (Equiv.apply_symm_apply (finCycle i1) i2)
  have hshift_i3 : (i3 - i1) + i1 = i3 := by
    simpa [finCycle] using (Equiv.apply_symm_apply (finCycle i1) i3)
  have hi2_ne_i1 : i2 ≠ i1 := by
    intro h
    exact S.triangle.v12_ne (by simpa [hi1, hi2] using congrArg phi h.symm)
  have hi3_ne_i1 : i3 ≠ i1 := by
    intro h
    exact S.triangle.v13_ne (by simpa [hi1, hi3] using congrArg phi h.symm)
  have hi2_ne_i3 : i2 ≠ i3 := by
    intro h
    exact S.triangle.v23_ne (by simpa [hi2, hi3] using congrArg phi h)
  have hi2_pos : i0 < i2 - i1 := by
    exact Fin.pos_iff_ne_zero.mpr (by
      intro h0
      apply hi2_ne_i1
      have h := congrArg (fun t : Fin n => t + i1) h0
      simpa [i0, hshift_i2] using h)
  have hi3_pos : i0 < i3 - i1 := by
    exact Fin.pos_iff_ne_zero.mpr (by
      intro h0
      apply hi3_ne_i1
      have h := congrArg (fun t : Fin n => t + i1) h0
      simpa [i0, hshift_i3] using h)
  have hcyc {a b c : ℝ²} :
      Problem97.signedArea2 a b c = Problem97.signedArea2 c a b := by
    simp [Problem97.signedArea2]
    ring
  have hswap {a b c : ℝ²} :
      Problem97.signedArea2 a b c = -Problem97.signedArea2 a c b := by
    simp [Problem97.signedArea2]
  by_cases h23 : i2 - i1 < i3 - i1
  · have hpsi_i2 : psi (i2 - i1) = S.triangle.v2 := by
      simpa [psi, hshift_i2] using hi2
    have hpsi_i3 : psi (i3 - i1) = S.triangle.v3 := by
      simpa [psi, hshift_i3] using hi3
    have hC1_interval :
        ∀ x : ℝ², x ∈ S.CP.C1 ↔
          ∃ q : Fin n, i2 - i1 ≤ q ∧ q ≤ i3 - i1 ∧ psi q = x := by
      simpa [psi, hshift_i2, hshift_i3] using
        b3n9m054_supportCap_interval_of_oppositeFirst_local
          (A := A) (C := S.CP.C1) (phi := psi)
          hpsi_inj hpsi_image hneg_shift S.CP.C1_subset
          (fun x hxA => (S.CP.arc_membership x hxA).1)
          S.CP.v2_mem_C1 S.CP.v3_mem_C1
          (u_idx := i0) (v_idx := i2 - i1) (w_idx := i3 - i1)
          hpsi0 hpsi_i2 hpsi_i3 hi2_pos h23
    rcases (hC1_interval p).1 hpC1 with ⟨q, hqlo, hqhi, hqeq⟩
    have hq_ne_left : q ≠ i2 - i1 := by
      intro hq
      apply hp_ne_v2
      calc
        p = psi q := hqeq.symm
        _ = psi (i2 - i1) := by simp [hq]
        _ = S.triangle.v2 := hpsi_i2
    have hq_ne_right : q ≠ i3 - i1 := by
      intro hq
      apply hp_ne_v3
      calc
        p = psi q := hqeq.symm
        _ = psi (i3 - i1) := by simp [hq]
        _ = S.triangle.v3 := hpsi_i3
    have hqgt : i2 - i1 < q := lt_of_le_of_ne hqlo hq_ne_left.symm
    have hqlt3 : q < i3 - i1 := lt_of_le_of_ne hqhi hq_ne_right
    have hp_neg :
        Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi q) < 0 := hneg_shift hi2_pos hqgt
    have hv3_neg :
        Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi (i3 - i1)) < 0 := hneg_shift hi2_pos h23
    have hp_side : Problem97.signedArea2 p S.triangle.v1 S.triangle.v2 < 0 := by
      rw [← hqeq, ← hpsi0, ← hpsi_i2]
      simpa [hcyc] using hp_neg
    have hv3_side :
        Problem97.signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 < 0 := by
      rw [← hpsi0, ← hpsi_i2, ← hpsi_i3]
      simpa [hcyc] using hv3_neg
    exact mul_pos_of_neg_of_neg hp_side hv3_side
  · have h32 : i3 - i1 < i2 - i1 := by
      have hle : i3 - i1 ≤ i2 - i1 := le_of_not_gt h23
      have hne : i3 - i1 ≠ i2 - i1 := by
        intro h
        apply hi2_ne_i3
        have h' := congrArg (fun t : Fin n => t + i1) h
        simpa [hshift_i2, hshift_i3] using h'.symm
      exact lt_of_le_of_ne hle hne
    have hpsi_i2 : psi (i2 - i1) = S.triangle.v2 := by
      simpa [psi, hshift_i2] using hi2
    have hpsi_i3 : psi (i3 - i1) = S.triangle.v3 := by
      simpa [psi, hshift_i3] using hi3
    have hC1_arc_swap :
        ∀ x ∈ A,
          x ∈ S.CP.C1 ↔ Problem97.OnArcOpposite S.triangle.v1 S.triangle.v3 S.triangle.v2 x := by
      intro x hxA
      have hC1_arc := (S.CP.arc_membership x hxA).1
      constructor
      · intro hx
        have hx' : Problem97.OnArcOpposite S.triangle.v1 S.triangle.v2 S.triangle.v3 x :=
          hC1_arc.mp hx
        unfold Problem97.OnArcOpposite at hx' ⊢
        have hxswap : signedArea2 x S.triangle.v3 S.triangle.v2 =
            -signedArea2 x S.triangle.v2 S.triangle.v3 := by
          simpa using (hswap (a := x) (b := S.triangle.v3) (c := S.triangle.v2))
        have hvswap : signedArea2 S.triangle.v1 S.triangle.v3 S.triangle.v2 =
            -signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 := by
          simpa using (hswap (a := S.triangle.v1) (b := S.triangle.v3) (c := S.triangle.v2))
        calc
          signedArea2 x S.triangle.v3 S.triangle.v2 *
              signedArea2 S.triangle.v1 S.triangle.v3 S.triangle.v2
              = (-signedArea2 x S.triangle.v2 S.triangle.v3) *
                  (-signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3) := by
                    rw [hxswap, hvswap]
          _ = signedArea2 x S.triangle.v2 S.triangle.v3 *
                signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 := by ring
          _ ≤ 0 := hx'
      · intro hx
        have hx' : Problem97.OnArcOpposite S.triangle.v1 S.triangle.v3 S.triangle.v2 x :=
          hx
        unfold Problem97.OnArcOpposite at hx'
        have hxswap : signedArea2 x S.triangle.v2 S.triangle.v3 =
            -signedArea2 x S.triangle.v3 S.triangle.v2 := by
          simpa using (hswap (a := x) (b := S.triangle.v2) (c := S.triangle.v3))
        have hvswap : signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 =
            -signedArea2 S.triangle.v1 S.triangle.v3 S.triangle.v2 := by
          simpa using (hswap (a := S.triangle.v1) (b := S.triangle.v2) (c := S.triangle.v3))
        have : signedArea2 x S.triangle.v2 S.triangle.v3 *
            signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 ≤ 0 := by
          calc
            signedArea2 x S.triangle.v2 S.triangle.v3 *
                signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3
                = (-signedArea2 x S.triangle.v3 S.triangle.v2) *
                    (-signedArea2 S.triangle.v1 S.triangle.v3 S.triangle.v2) := by
                      rw [hxswap, hvswap]
            _ = signedArea2 x S.triangle.v3 S.triangle.v2 *
                  signedArea2 S.triangle.v1 S.triangle.v3 S.triangle.v2 := by ring
            _ ≤ 0 := hx'
        exact hC1_arc.mpr this
    have hC1_interval :
        ∀ x : ℝ², x ∈ S.CP.C1 ↔
          ∃ q : Fin n, i3 - i1 ≤ q ∧ q ≤ i2 - i1 ∧ psi q = x := by
      simpa [psi, hshift_i2, hshift_i3] using
        b3n9m054_supportCap_interval_of_oppositeFirst_local
          (A := A) (C := S.CP.C1) (phi := psi)
          hpsi_inj hpsi_image hneg_shift S.CP.C1_subset
          hC1_arc_swap S.CP.v3_mem_C1 S.CP.v2_mem_C1
          (u_idx := i0) (v_idx := i3 - i1) (w_idx := i2 - i1)
          hpsi0 hpsi_i3 hpsi_i2 hi3_pos h32
    rcases (hC1_interval p).1 hpC1 with ⟨q, hqlo, hqhi, hqeq⟩
    have hq_ne_left : q ≠ i3 - i1 := by
      intro hq
      apply hp_ne_v3
      calc
        p = psi q := hqeq.symm
        _ = psi (i3 - i1) := by simp [hq]
        _ = S.triangle.v3 := hpsi_i3
    have hq_ne_right : q ≠ i2 - i1 := by
      intro hq
      apply hp_ne_v2
      calc
        p = psi q := hqeq.symm
        _ = psi (i2 - i1) := by simp [hq]
        _ = S.triangle.v2 := hpsi_i2
    have hqgt : i3 - i1 < q := lt_of_le_of_ne hqlo hq_ne_left.symm
    have hqlt2 : q < i2 - i1 := lt_of_le_of_ne hqhi hq_ne_right
    have hp_mid :
        Problem97.signedArea2 (psi i0) (psi q) (psi (i2 - i1)) < 0 :=
      hneg_shift (lt_trans hi3_pos hqgt) hqlt2
    have hv3_mid :
        Problem97.signedArea2 (psi i0) (psi (i3 - i1)) (psi (i2 - i1)) < 0 :=
      hneg_shift hi3_pos h32
    have hp_side : 0 < Problem97.signedArea2 p S.triangle.v1 S.triangle.v2 := by
      rw [← hqeq, ← hpsi0, ← hpsi_i2]
      have hq_side : 0 < Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi q) := by
        have hswap_q :
            Problem97.signedArea2 (psi i0) (psi q) (psi (i2 - i1)) =
              -Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi q) := by
          simpa using (hswap (a := psi i0) (b := psi q) (c := psi (i2 - i1)))
        have : -Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi q) < 0 := by
          rw [← hswap_q]
          exact hp_mid
        linarith
      simpa [hcyc] using hq_side
    have hv3_side : 0 < Problem97.signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 := by
      rw [← hpsi0, ← hpsi_i2, ← hpsi_i3]
      have hv3_side' : 0 < Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi (i3 - i1)) := by
        have hswap_3 :
            Problem97.signedArea2 (psi i0) (psi (i3 - i1)) (psi (i2 - i1)) =
              -Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi (i3 - i1)) := by
          simpa using (hswap (a := psi i0) (b := psi (i3 - i1)) (c := psi (i2 - i1)))
        have : -Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi (i3 - i1)) < 0 := by
          rw [← hswap_3]
          exact hv3_mid
        linarith
      simpa [hcyc] using hv3_side'
    exact mul_pos hp_side hv3_side

end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit054

-- Original module: Solutions.Batch3N9.N4d.FaithfulFrame
section Batch3N9Unit060
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
theorem b3n9m060_dist_sq_eq_coord_sq_add_coord_sq (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 :=
  Problem97.dist_sq_coord x y
noncomputable def b3n9m060_similarityTransportComp
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
noncomputable def b3n9m060_halfShift (p : ℝ²) : ℝ² :=
  Problem97.CGN.vec2 ((p 0 + 1) / 2) (p 1 / 2)
theorem b3n9m060_halfShift_injective : Function.Injective b3n9m060_halfShift := by
  intro p q hpq
  ext i <;> fin_cases i
  · have h := congrArg (fun z : ℝ² => z 0) hpq
    simpa [b3n9m060_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply] using h
  · have h := congrArg (fun z : ℝ² => z 1) hpq
    simpa [b3n9m060_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply] using h
noncomputable def b3n9m060_halfShiftSimilarityTransportData :
    Problem97.CGN.SimilarityTransportData b3n9m060_halfShift := by
  classical
  let F : ℝ² →ₗ[ℝ] ℝ² := (1 / 2 : ℝ) • LinearMap.id
  let c : ℝ² := Problem97.CGN.vec2 ((1 : ℝ) / 2) 0
  let Taff : ℝ² →ᵃ[ℝ] ℝ² := AffineMap.mk' b3n9m060_halfShift F c (by
    intro p
    ext i <;> fin_cases i <;>
      simp [b3n9m060_halfShift, F, c, Problem97.CGN.vec2, EuclideanSpace.single_apply, Pi.add_apply]
    · ring
    · ring
    )
  have hdist0 : ∀ a b : ℝ², dist (b3n9m060_halfShift a) (b3n9m060_halfShift b) = ((1 : ℝ) / 2) * dist a b := by
    intro a b
    have hcoord :
        b3n9m060_halfShift a - b3n9m060_halfShift b =
          (1 / 2 : ℝ) • (a - b) := by
      ext i <;> fin_cases i <;>
        simp [b3n9m060_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply, sub_eq_add_neg]
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
    have hmap : b3n9m060_halfShift '' convexHull ℝ S = convexHull ℝ (b3n9m060_halfShift '' S) := by
      simpa [Taff] using (AffineMap.image_convexHull Taff S)
    constructor
    · intro ha
      rw [← hmap] at ha
      rcases ha with ⟨b, hb, hTb⟩
      have hba : b = a := b3n9m060_halfShift_injective hTb
      simpa [hba] using hb
    · intro ha
      simpa [hmap] using (show b3n9m060_halfShift a ∈ b3n9m060_halfShift '' convexHull ℝ S from ⟨a, ha, rfl⟩)
  · intro a b c
    unfold b3n9m060_halfShift
    simp [Problem97.signedArea2, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    ring
noncomputable def b3n9m060_flipY (p : ℝ²) : ℝ² :=
  Problem97.CGN.vec2 (p 0) (-p 1)
theorem b3n9m060_flipY_injective : Function.Injective b3n9m060_flipY := by
  intro p q hpq
  ext i <;> fin_cases i
  · have h := congrArg (fun z : ℝ² => z 0) hpq
    simpa [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply] using h
  · have h := congrArg (fun z : ℝ² => z 1) hpq
    simpa [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply] using h
noncomputable def b3n9m060_flipYSimilarityTransportData :
    Problem97.CGN.SimilarityTransportData b3n9m060_flipY := by
  classical
  let F : ℝ² →ₗ[ℝ] ℝ² :=
    { toFun := b3n9m060_flipY
      map_add' := by
        intro x y
        ext i <;> fin_cases i <;>
          simp [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
        · ring
      map_smul' := by
        intro r x
        ext i <;> fin_cases i <;>
          simp [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
      }
  let Taff : ℝ² →ᵃ[ℝ] ℝ² := AffineMap.mk' b3n9m060_flipY F 0 (by
    intro p
    ext i <;> fin_cases i <;>
      simp [b3n9m060_flipY, F, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    )
  have hdist0 : ∀ a b : ℝ², dist (b3n9m060_flipY a) (b3n9m060_flipY b) = dist a b := by
    intro a b
    have hsq :
        ‖b3n9m060_flipY a - b3n9m060_flipY b‖ ^ 2 = ‖a - b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply, Fin.sum_univ_two, sq_abs,
        Real.norm_eq_abs, PiLp.sub_apply]
      ring
    have hnonneg1 : 0 ≤ ‖b3n9m060_flipY a - b3n9m060_flipY b‖ := norm_nonneg _
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
    have hmap : b3n9m060_flipY '' convexHull ℝ S = convexHull ℝ (b3n9m060_flipY '' S) := by
      simpa [Taff] using (AffineMap.image_convexHull Taff S)
    constructor
    · intro ha
      rw [← hmap] at ha
      rcases ha with ⟨b, hb, hTb⟩
      have hba : b = a := b3n9m060_flipY_injective hTb
      simpa [hba] using hb
    · intro ha
      simpa [hmap] using (show b3n9m060_flipY a ∈ b3n9m060_flipY '' convexHull ℝ S from ⟨a, ha, rfl⟩)
  · intro a b c
    unfold b3n9m060_flipY
    simp [Problem97.signedArea2, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    ring
theorem b3n9m060_vec2_coord0 (x y : ℝ) : (Problem97.CGN.vec2 x y) 0 = x := by
  simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
theorem b3n9m060_vec2_coord1 (x y : ℝ) : (Problem97.CGN.vec2 x y) 1 = y := by
  simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
theorem b3n9m060_dist_vec2_00_10 :
    dist (Problem97.CGN.vec2 (0 : ℝ) 0) (Problem97.CGN.vec2 (1 : ℝ) 0) = 1 := by
  have hsq : dist (Problem97.CGN.vec2 (0 : ℝ) 0) (Problem97.CGN.vec2 (1 : ℝ) 0) ^ 2 = 1 := by
    rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq]
    simp [b3n9m060_vec2_coord0, b3n9m060_vec2_coord1]
  have hnn : 0 ≤ dist (Problem97.CGN.vec2 (0 : ℝ) 0) (Problem97.CGN.vec2 (1 : ℝ) 0) :=
    dist_nonneg
  calc dist (Problem97.CGN.vec2 (0 : ℝ) 0) (Problem97.CGN.vec2 (1 : ℝ) 0)
      = Real.sqrt (dist (Problem97.CGN.vec2 (0 : ℝ) 0) (Problem97.CGN.vec2 (1 : ℝ) 0) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ = Real.sqrt 1 := by rw [hsq]
    _ = 1 := Real.sqrt_one
theorem b3n9m060_signedArea2_chart_base (p : ℝ²) :
    signedArea2 p (Problem97.CGN.vec2 0 0) (Problem97.CGN.vec2 1 0) = p 1 := by
  simp [Problem97.signedArea2, Problem97.CGN.vec2, EuclideanSpace.single_apply]
  ring
theorem b3n9m060_v2v1_dist_of_hexact
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S) {s : ℝ}
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    dist S.triangle.v2 S.triangle.v1 = s := by
  have hmem : S.triangle.v1 ∈ S.witnessClassAt_v2 s := by
    rw [hexact]; simp
  simpa using (Finset.mem_filter.mp hmem).2
theorem b3n9m060_v2v3_dist_of_hexact
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S) {s : ℝ}
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    dist S.triangle.v2 S.triangle.v3 = s := by
  have hmem : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
    rw [hexact]; simp
  simpa using (Finset.mem_filter.mp hmem).2
theorem b3n9m060_v2a2_dist_of_hexact
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S) {s : ℝ}
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    dist S.triangle.v2 Z.a2 = s := by
  have hmem : Z.a2 ∈ S.witnessClassAt_v2 s := by
    rw [hexact]; simp
  simpa using (Finset.mem_filter.mp hmem).2
theorem b3n9m060_v2b2_dist_of_hexact
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S) {s : ℝ}
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    dist S.triangle.v2 Z.b2 = s := by
  have hmem : Z.b2 ∈ S.witnessClassAt_v2 s := by
    rw [hexact]; simp
  simpa using (Finset.mem_filter.mp hmem).2
structure NormBase {A : Finset ℝ²} (S : FiniteEndpointShell A) where
  T : ℝ² → ℝ²
  tau : Problem97.CGN.SimilarityTransportData T
  hv1 : T S.triangle.v1 = Problem97.CGN.vec2 0 0
  hv2 : T S.triangle.v2 = Problem97.CGN.vec2 1 0
  hv3y_pos : 0 < (T S.triangle.v3) 1
theorem b3n9m060_exists_v2_normalized_transport
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    ∃ T : ℝ² → ℝ², ∃ tau : Problem97.CGN.SimilarityTransportData T,
      T S.triangle.v1 = Problem97.CGN.vec2 0 0 ∧
      T S.triangle.v2 = Problem97.CGN.vec2 1 0 ∧
      0 < (T S.triangle.v3) 1 := by
  classical
  obtain ⟨T0, tau0, hT0v1, hT0v2⟩ :=
    (p2mCoreSupport S).exists_base_transportData S.triangle.v1 S.triangle.v2 S.triangle.v12_ne
  have hhalf_neg : b3n9m060_halfShift (Problem97.CGN.vec2 (-1) 0) = Problem97.CGN.vec2 0 0 := by
    ext i <;> fin_cases i <;>
      simp [b3n9m060_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply] <;> norm_num
  have hhalf_one : b3n9m060_halfShift (Problem97.CGN.vec2 1 0) = Problem97.CGN.vec2 1 0 := by
    ext i <;> fin_cases i <;>
      simp [b3n9m060_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply] <;> norm_num
  let T1 : ℝ² → ℝ² := fun x => b3n9m060_halfShift (T0 x)
  let tau1 : Problem97.CGN.SimilarityTransportData T1 :=
    b3n9m060_similarityTransportComp tau0 b3n9m060_halfShiftSimilarityTransportData
  have hT1v1 : T1 S.triangle.v1 = Problem97.CGN.vec2 0 0 := by
    change b3n9m060_halfShift (T0 S.triangle.v1) = _
    rw [hT0v1, hhalf_neg]
  have hT1v2 : T1 S.triangle.v2 = Problem97.CGN.vec2 1 0 := by
    change b3n9m060_halfShift (T0 S.triangle.v2) = _
    rw [hT0v2, hhalf_one]
  have hbd1 : dist S.triangle.v1 S.Packet.center = S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.moser_on_boundary_1
  have hbd2 : dist S.triangle.v2 S.Packet.center = S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.moser_on_boundary_2
  have hbd3 : dist S.triangle.v3 S.Packet.center = S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.moser_on_boundary_3
  have hsa0 : signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 ≠ 0 :=
    Problem97.MEC.signedArea2_ne_zero_of_three_dist_eq hbd3 hbd1 hbd2
      S.triangle.v13_ne.symm S.triangle.v12_ne S.triangle.v23_ne.symm
  have hv3_off : (T1 S.triangle.v3) 1 ≠ 0 := by
    intro hzero
    have harea : signedArea2 (T1 S.triangle.v3) (T1 S.triangle.v1) (T1 S.triangle.v2) = 0 := by
      rw [hT1v1, hT1v2, b3n9m060_signedArea2_chart_base, hzero]
    have htrans := tau1.halfplane_sign S.triangle.v3 S.triangle.v1 S.triangle.v2
    rw [harea] at htrans
    have ho : tau1.orientation ≠ 0 := by
      intro h0
      have := tau1.orientation_sq
      rw [h0] at this; norm_num at this
    have hsc : tau1.scale ^ 2 ≠ 0 := pow_ne_zero 2 tau1.scale_pos.ne'
    have : signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 = 0 := by
      have hcoef : tau1.orientation * tau1.scale ^ 2 ≠ 0 := mul_ne_zero ho hsc
      rcases mul_eq_zero.mp htrans.symm with h | h
      · exact absurd h hcoef
      · exact h
    exact hsa0 this
  rcases lt_trichotomy ((T1 S.triangle.v3) 1) 0 with hneg | hzero | hpos
  ·
    have hflip00 : b3n9m060_flipY (Problem97.CGN.vec2 0 0) = Problem97.CGN.vec2 0 0 := by
      ext i <;> fin_cases i <;>
        simp [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hflip10 : b3n9m060_flipY (Problem97.CGN.vec2 1 0) = Problem97.CGN.vec2 1 0 := by
      ext i <;> fin_cases i <;>
        simp [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hflipy : ∀ p : ℝ², (b3n9m060_flipY p) 1 = -(p 1) := by
      intro p
      simp [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    let T2 : ℝ² → ℝ² := fun x => b3n9m060_flipY (T1 x)
    let tau2 : Problem97.CGN.SimilarityTransportData T2 :=
      b3n9m060_similarityTransportComp tau1 b3n9m060_flipYSimilarityTransportData
    refine ⟨T2, tau2, ?_, ?_, ?_⟩
    · change b3n9m060_flipY (T1 S.triangle.v1) = _; rw [hT1v1, hflip00]
    · change b3n9m060_flipY (T1 S.triangle.v2) = _; rw [hT1v2, hflip10]
    · change 0 < (b3n9m060_flipY (T1 S.triangle.v3)) 1; rw [hflipy]; linarith
  · exact absurd hzero hv3_off
  · exact ⟨T1, tau1, hT1v1, hT1v2, hpos⟩
noncomputable def normBase {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    NormBase S :=
  Classical.choice (by
    obtain ⟨T, tau, hv1, hv2, hv3y_pos⟩ := S.b3n9m060_exists_v2_normalized_transport
    exact ⟨⟨T, tau, hv1, hv2, hv3y_pos⟩⟩)
structure V2AnchorFrame {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) where
  T : ℝ² → ℝ²
  tau : Problem97.CGN.SimilarityTransportData T
  c : ℝ
  sg : ℝ
  Oy : ℝ
  hv1 : T S.triangle.v1 = Problem97.CGN.vec2 0 0
  hv2 : T S.triangle.v2 = Problem97.CGN.vec2 1 0
  hv3 : T S.triangle.v3 = Problem97.CGN.vec2 (1 + c) sg
  hO : T S.Packet.center = Problem97.CGN.vec2 (1 / 2) Oy
  hcsg : c ^ 2 + sg ^ 2 = 1
  hsg_pos : 0 < sg
  hc_le : c ≤ 0
  hOy_pos : 0 < Oy
  hmec : 2 * sg * Oy = 1 + c
  hcirc_v1 : dist (T S.triangle.v2) (T S.triangle.v1) = 1
  hcirc_v3 : dist (T S.triangle.v2) (T S.triangle.v3) = 1
  hcirc_a2 : dist (T S.triangle.v2) (T Z.a2) = 1
  hcirc_b2 : dist (T S.triangle.v2) (T Z.b2) = 1
  ha2_y : 0 < (T Z.a2) 1
  hb2_y : 0 < (T Z.b2) 1
  hv2_on_mec : dist (T S.triangle.v2) (T S.Packet.center) ^ 2 = 1 / 4 + Oy ^ 2
  hdisk : ∀ x ∈ A, dist (T x) (T S.Packet.center) ^ 2 ≤ 1 / 4 + Oy ^ 2
  ha3_y : (T Z.a3) 1 ≤ 0
  hb3_y : (T Z.b3) 1 ≤ 0
theorem b3n9m060_chart_signedArea_eq_coord1 {T : ℝ² → ℝ²}
    {v1 v2 p : ℝ²}
    (hv1 : T v1 = Problem97.CGN.vec2 0 0) (hv2 : T v2 = Problem97.CGN.vec2 1 0) :
    signedArea2 (T p) (T v1) (T v2) = (T p) 1 := by
  rw [hv1, hv2, b3n9m060_signedArea2_chart_base]
theorem b3n9m060_chart_y_product {T : ℝ² → ℝ²}
    (tau : Problem97.CGN.SimilarityTransportData T) {v1 v2 p q : ℝ²}
    (hv1 : T v1 = Problem97.CGN.vec2 0 0) (hv2 : T v2 = Problem97.CGN.vec2 1 0) :
    (T p) 1 * (T q) 1 =
      tau.scale ^ 4 *
        (signedArea2 p v1 v2 * signedArea2 q v1 v2) := by
  have hp := tau.halfplane_sign p v1 v2
  have hq := tau.halfplane_sign q v1 v2
  rw [b3n9m060_chart_signedArea_eq_coord1 hv1 hv2] at hp
  rw [b3n9m060_chart_signedArea_eq_coord1 hv1 hv2] at hq
  have hkey : (T p) 1 * (T q) 1
      = (tau.orientation ^ 2 * tau.scale ^ 4) *
        (signedArea2 p v1 v2 * signedArea2 q v1 v2) := by
    rw [hp, hq]; ring
  rw [hkey, tau.orientation_sq, one_mul]
theorem b3n9m060_frame_c3_lower
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {x : ℝ²}
    {T : ℝ² → ℝ²} (tau : Problem97.CGN.SimilarityTransportData T)
    (hv1 : T S.triangle.v1 = Problem97.CGN.vec2 0 0)
    (hv2 : T S.triangle.v2 = Problem97.CGN.vec2 1 0)
    (hsg_pos : 0 < (T S.triangle.v3) 1)
    (hxI3 : x ∈ S.I3) :
    (T x) 1 ≤ 0 := by
  have hxC3 : x ∈ S.CP.C3 :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hxI3).2).2
  have hxA : x ∈ A := S.CP.C3_subset hxC3
  have hopp : Problem97.OnArcOpposite S.triangle.v3 S.triangle.v1 S.triangle.v2 x :=
    ((S.CP.arc_membership x hxA).2.2.mp hxC3)
  unfold Problem97.OnArcOpposite at hopp
  have hy := b3n9m060_chart_y_product (T := T) tau (p := x) (q := S.triangle.v3) hv1 hv2
  have hle : (T x) 1 * (T S.triangle.v3) 1 ≤ 0 := by
    rw [hy]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hopp
  nlinarith only [hle, hsg_pos]
theorem b3n9m060_frame_c2_upper
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {p : ℝ²}
    {T : ℝ² → ℝ²} (tau : Problem97.CGN.SimilarityTransportData T)
    (hv1 : T S.triangle.v1 = Problem97.CGN.vec2 0 0)
    (hv2 : T S.triangle.v2 = Problem97.CGN.vec2 1 0)
    (hsg_pos : 0 < (T S.triangle.v3) 1)
    (hpI2 : p ∈ S.I2) :
    0 < (T p) 1 := by
  have hside := (p2mCoreSupport S).c2_vertex_same_open_side_as_v3 hpI2
  have hy := b3n9m060_chart_y_product (T := T) tau (p := p) (q := S.triangle.v3) hv1 hv2
  have hpos : 0 < (T p) 1 * (T S.triangle.v3) 1 := by
    rw [hy]; exact mul_pos (pow_pos tau.scale_pos 4) hside
  nlinarith only [hpos, hsg_pos]
theorem b3n9m060_frame_a2_upper
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S)
    {T : ℝ² → ℝ²} (tau : Problem97.CGN.SimilarityTransportData T)
    (hv1 : T S.triangle.v1 = Problem97.CGN.vec2 0 0)
    (hv2 : T S.triangle.v2 = Problem97.CGN.vec2 1 0)
    (hsg_pos : 0 < (T S.triangle.v3) 1) :
    0 < (T Z.a2) 1 :=
  S.b3n9m060_frame_c2_upper tau hv1 hv2 hsg_pos (by rw [Z.hI2]; simp)
theorem b3n9m060_frame_disk
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {Oy R : ℝ}
    {T : ℝ² → ℝ²} (tau : Problem97.CGN.SimilarityTransportData T)
    (hR : R = tau.scale * S.Packet.radius)
    (hRsq : R ^ 2 = 1 / 4 + Oy ^ 2) :
    ∀ x ∈ A, dist (T x) (T S.Packet.center) ^ 2 ≤ 1 / 4 + Oy ^ 2 := by
  intro x hx
  have hxdisk : dist x S.Packet.center ≤ S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.disk_contains_A x hx
  have hle : dist (T x) (T S.Packet.center) ≤ R := by
    rw [tau.dist_image, hR]
    exact mul_le_mul_of_nonneg_left hxdisk tau.scale_pos.le
  have hsq : dist (T x) (T S.Packet.center) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ dist_nonneg hle 2
  rw [hRsq] at hsq; exact hsq
set_option maxHeartbeats 4000000 in
theorem b3n9m060_v2AnchorFrame_facts
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S) {s : ℝ}
    (T : ℝ² → ℝ²) (tau : Problem97.CGN.SimilarityTransportData T)
    (hv1 : T S.triangle.v1 = Problem97.CGN.vec2 0 0)
    (hv2 : T S.triangle.v2 = Problem97.CGN.vec2 1 0)
    (hv3y_pos : 0 < (T S.triangle.v3) 1)
    (hv2v1 : dist S.triangle.v2 S.triangle.v1 = s)
    (hv2v3 : dist S.triangle.v2 S.triangle.v3 = s)
    (hv2a2 : dist S.triangle.v2 Z.a2 = s)
    (hv2b2 : dist S.triangle.v2 Z.b2 = s) :
    ∃ c sg Oy : ℝ,
      T S.triangle.v3 = Problem97.CGN.vec2 (1 + c) sg ∧
      T S.Packet.center = Problem97.CGN.vec2 (1 / 2) Oy ∧
      c ^ 2 + sg ^ 2 = 1 ∧ 0 < sg ∧ c ≤ 0 ∧ 0 < Oy ∧ 2 * sg * Oy = 1 + c ∧
      dist (T S.triangle.v2) (T S.triangle.v1) = 1 ∧
      dist (T S.triangle.v2) (T S.triangle.v3) = 1 ∧
      dist (T S.triangle.v2) (T Z.a2) = 1 ∧
      dist (T S.triangle.v2) (T Z.b2) = 1 ∧
      0 < (T Z.a2) 1 ∧
      0 < (T Z.b2) 1 ∧
      dist (T S.triangle.v2) (T S.Packet.center) ^ 2 = 1 / 4 + Oy ^ 2 ∧
      (∀ x ∈ A, dist (T x) (T S.Packet.center) ^ 2 ≤ 1 / 4 + Oy ^ 2) ∧
      (T Z.a3) 1 ≤ 0 ∧ (T Z.b3) 1 ≤ 0 := by
  classical
  have hs_pos : 0 < s := by
    rw [← hv2v1]; exact dist_pos.mpr S.triangle.v12_ne.symm
  have hscale : tau.scale * s = 1 := by
    have hbase : dist (T S.triangle.v2) (T S.triangle.v1) = tau.scale * s := by
      rw [tau.dist_image, hv2v1]
    have hone : dist (T S.triangle.v2) (T S.triangle.v1) = 1 := by
      rw [hv2, hv1, dist_comm, b3n9m060_dist_vec2_00_10]
    rw [← hbase, hone]
  set c := (T S.triangle.v3) 0 - 1 with hc_def
  set sg := (T S.triangle.v3) 1 with hsg_def
  set Oy := (T S.Packet.center) 1 with hOy_def
  have hv3 : T S.triangle.v3 = Problem97.CGN.vec2 (1 + c) sg := by
    ext i
    fin_cases i
    · change (T S.triangle.v3) 0 = (Problem97.CGN.vec2 (1 + c) sg) 0
      rw [b3n9m060_vec2_coord0, hc_def]; ring
    · change (T S.triangle.v3) 1 = (Problem97.CGN.vec2 (1 + c) sg) 1
      rw [b3n9m060_vec2_coord1, hsg_def]
  have hsg_pos : 0 < sg := hv3y_pos
  have hcirc_v1 : dist (T S.triangle.v2) (T S.triangle.v1) = 1 := by
    rw [tau.dist_image, hv2v1, hscale]
  have hcirc_v3 : dist (T S.triangle.v2) (T S.triangle.v3) = 1 := by
    rw [tau.dist_image, hv2v3, hscale]
  have hcirc_a2 : dist (T S.triangle.v2) (T Z.a2) = 1 := by
    rw [tau.dist_image, hv2a2, hscale]
  have hcirc_b2 : dist (T S.triangle.v2) (T Z.b2) = 1 := by
    rw [tau.dist_image, hv2b2, hscale]
  have hc3sq : dist (T S.triangle.v2) (T S.triangle.v3) ^ 2 = 1 := by
    rw [hcirc_v3]; norm_num
  set R := tau.scale * S.Packet.radius with hR_def
  have hbd1 : dist S.triangle.v1 S.Packet.center = S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.moser_on_boundary_1
  have hbd2 : dist S.triangle.v2 S.Packet.center = S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.moser_on_boundary_2
  have hbd3 : dist S.triangle.v3 S.Packet.center = S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.moser_on_boundary_3
  have hb1sq : dist (T S.triangle.v1) (T S.Packet.center) ^ 2 = R ^ 2 := by
    rw [tau.dist_image, hbd1, hR_def]
  have hb2sq : dist (T S.triangle.v2) (T S.Packet.center) ^ 2 = R ^ 2 := by
    rw [tau.dist_image, hbd2, hR_def]
  have hb3sq : dist (T S.triangle.v3) (T S.Packet.center) ^ 2 = R ^ 2 := by
    rw [tau.dist_image, hbd3, hR_def]
  set ox := (T S.Packet.center) 0 with hox_def
  have e1 : ox ^ 2 + Oy ^ 2 = R ^ 2 := by
    have h := hb1sq
    rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, hv1, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1] at h
    simpa [hox_def, hOy_def] using h
  have e2 : (1 - ox) ^ 2 + Oy ^ 2 = R ^ 2 := by
    have h := hb2sq
    rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, hv2, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1] at h
    have h' : ((1 : ℝ) - ox) ^ 2 + Oy ^ 2 = R ^ 2 := by nlinarith only [h]
    exact h'
  have e3 : (1 + c - ox) ^ 2 + (sg - Oy) ^ 2 = R ^ 2 := by
    have h := hb3sq
    rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, hv3, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1] at h
    exact h
  have ec : c ^ 2 + sg ^ 2 = 1 := by
    have h := hc3sq
    rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, hv2, hv3, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1,
      b3n9m060_vec2_coord0, b3n9m060_vec2_coord1] at h
    nlinarith only [h]
  clear_value c sg Oy ox R
  have hox : ox = 1 / 2 := by nlinarith only [e1, e2]
  have hcsg : c ^ 2 + sg ^ 2 = 1 := ec
  have hmec : 2 * sg * Oy = 1 + c := by nlinarith only [e1, e3, ec, e2, hox]
  have hRsq : R ^ 2 = 1 / 4 + Oy ^ 2 := by nlinarith only [e1, e2, hox]
  have hv2_on_mec : dist (T S.triangle.v2) (T S.Packet.center) ^ 2 = 1 / 4 + Oy ^ 2 := by
    rw [hb2sq, hRsq]
  have hO : T S.Packet.center = Problem97.CGN.vec2 (1 / 2) Oy := by
    ext i
    fin_cases i
    · change (T S.Packet.center) 0 = (Problem97.CGN.vec2 (1 / 2) Oy) 0
      rw [b3n9m060_vec2_coord0, ← hox_def]; exact hox
    · change (T S.Packet.center) 1 = (Problem97.CGN.vec2 (1 / 2) Oy) 1
      rw [b3n9m060_vec2_coord1, hOy_def]
  have hc_le : c ≤ 0 := by
    have hpol : dist S.triangle.v1 S.triangle.v3 ^ 2 ≤ s ^ 2 + s ^ 2 := by
      have hinner := S.Packet.inner_at_v2
      have hexp := norm_sub_sq_real (S.triangle.v3 - S.triangle.v2)
        (S.triangle.v1 - S.triangle.v2)
      have hrw : S.triangle.v3 - S.triangle.v2 - (S.triangle.v1 - S.triangle.v2)
          = S.triangle.v3 - S.triangle.v1 := by abel
      rw [hrw] at hexp
      have h1 : ‖S.triangle.v3 - S.triangle.v1‖ = dist S.triangle.v1 S.triangle.v3 := by
        rw [← dist_eq_norm, dist_comm]
      have h2 : ‖S.triangle.v3 - S.triangle.v2‖ = s := by
        rw [← dist_eq_norm, dist_comm, hv2v3]
      have h3 : ‖S.triangle.v1 - S.triangle.v2‖ = s := by
        rw [← dist_eq_norm, dist_comm, hv2v1]
      rw [h1, h2, h3] at hexp
      nlinarith only [hinner, hexp]
    have htrans : dist (T S.triangle.v1) (T S.triangle.v3) ^ 2 ≤ 2 := by
      rw [tau.dist_image]
      calc (tau.scale * dist S.triangle.v1 S.triangle.v3) ^ 2
          = tau.scale ^ 2 * dist S.triangle.v1 S.triangle.v3 ^ 2 := by ring
        _ ≤ tau.scale ^ 2 * (s ^ 2 + s ^ 2) :=
            mul_le_mul_of_nonneg_left hpol (by positivity)
        _ = (tau.scale * s) ^ 2 + (tau.scale * s) ^ 2 := by ring
        _ = 2 := by rw [hscale]; norm_num
    have hexpand : dist (T S.triangle.v1) (T S.triangle.v3) ^ 2 = (1 + c) ^ 2 + sg ^ 2 := by
      rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, hv1, hv3, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1,
        b3n9m060_vec2_coord0, b3n9m060_vec2_coord1]
      ring
    rw [hexpand] at htrans
    nlinarith only [ec, htrans, hcsg]
  have hOy_pos : 0 < Oy := by
    have hcgt : -1 < c := by nlinarith only [e1, e2, hRsq, e3, ec, hmec, hv3y_pos, hcsg, hsg_pos]
    have h1c : 0 < 1 + c := by linarith
    have h2sg : 0 < 2 * sg := by linarith
    have hprod : 0 < 2 * sg * Oy := by rw [hmec]; exact h1c
    nlinarith only [hv3y_pos, hmec, hcgt, hprod, h2sg]
  have hv3y_pos' : 0 < (T S.triangle.v3) 1 := hsg_def ▸ hsg_pos
  have ha2_y : 0 < (T Z.a2) 1 := S.b3n9m060_frame_a2_upper Z tau hv1 hv2 hv3y_pos'
  have hb2_y : 0 < (T Z.b2) 1 :=
    S.b3n9m060_frame_c2_upper tau hv1 hv2 hv3y_pos' (by rw [Z.hI2]; simp)
  have ha3_y : (T Z.a3) 1 ≤ 0 :=
    S.b3n9m060_frame_c3_lower tau hv1 hv2 hv3y_pos' (by rw [Z.hI3]; simp)
  have hb3_y : (T Z.b3) 1 ≤ 0 :=
    S.b3n9m060_frame_c3_lower tau hv1 hv2 hv3y_pos' (by rw [Z.hI3]; simp)
  have hdisk : ∀ x ∈ A, dist (T x) (T S.Packet.center) ^ 2 ≤ 1 / 4 + Oy ^ 2 :=
    S.b3n9m060_frame_disk tau hR_def hRsq
  exact ⟨c, sg, Oy, hv3, hO, hcsg, hsg_pos, hc_le, hOy_pos, hmec, hcirc_v1, hcirc_v3,
    hcirc_a2, hcirc_b2, ha2_y, hb2_y, hv2_on_mec, hdisk, ha3_y, hb3_y⟩
noncomputable def v2AnchorFrame_of_hexact
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S) {s : ℝ}
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    V2AnchorFrame S Z := by
  classical
  obtain ⟨T, tau, hv1, hv2, hv3y_pos⟩ := S.normBase
  have hfacts := S.b3n9m060_v2AnchorFrame_facts Z T tau hv1 hv2 hv3y_pos
      (S.b3n9m060_v2v1_dist_of_hexact Z hexact)
      (S.b3n9m060_v2v3_dist_of_hexact Z hexact)
      (S.b3n9m060_v2a2_dist_of_hexact Z hexact)
      (S.b3n9m060_v2b2_dist_of_hexact Z hexact)
  set c := hfacts.choose with hc_eq
  set sg := hfacts.choose_spec.choose with hsg_eq
  set Oy := hfacts.choose_spec.choose_spec.choose with hOy_eq
  obtain ⟨hv3, hO, hcsg, hsg_pos, hc_le, hOy_pos, hmec, hcirc_v1, hcirc_v3,
      hcirc_a2, hcirc_b2, ha2_y, hb2_y, hv2_on_mec, hdisk, ha3_y, hb3_y⟩ :=
    hfacts.choose_spec.choose_spec.choose_spec
  exact
    { T := T
      tau := tau
      c := c
      sg := sg
      Oy := Oy
      hv1 := hv1
      hv2 := hv2
      hv3 := hv3
      hO := hO
      hcsg := hcsg
      hsg_pos := hsg_pos
      hc_le := hc_le
      hOy_pos := hOy_pos
      hmec := hmec
      hcirc_v1 := hcirc_v1
      hcirc_v3 := hcirc_v3
      hcirc_a2 := hcirc_a2
      hcirc_b2 := hcirc_b2
      ha2_y := ha2_y
      hb2_y := hb2_y
      hv2_on_mec := hv2_on_mec
      hdisk := hdisk
      ha3_y := ha3_y
      hb3_y := hb3_y }
theorem b3n9m060_v1_mem_A {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.triangle.v1 ∈ A :=
  S.triangle.v1_mem
theorem b3n9m060_v3_mem_A {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.triangle.v3 ∈ A :=
  S.triangle.v3_mem
theorem b3n9m060_a2_mem_A {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) : Z.a2 ∈ A := by
  have h : Z.a2 ∈ S.I2 := by rw [Z.hI2]; simp
  exact S.CP.C2_subset ((Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2)
theorem b3n9m060_b2_mem_A {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) : Z.b2 ∈ A := by
  have h : Z.b2 ∈ S.I2 := by rw [Z.hI2]; simp
  exact S.CP.C2_subset ((Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2)
namespace V2AnchorFrame
variable {A : Finset ℝ²} {S : FiniteEndpointShell A} {Z : ZeroDefectCapLayout S}
theorem T_injective (F : V2AnchorFrame S Z) : Function.Injective F.T := by
  intro a b hab
  by_contra hne
  have hd : 0 < dist a b := dist_pos.mpr hne
  have heq : dist (F.T a) (F.T b) = F.tau.scale * dist a b := F.tau.dist_image a b
  rw [hab, dist_self] at heq
  have hpos : 0 < F.tau.scale * dist a b := mul_pos F.tau.scale_pos hd
  rw [← heq] at hpos
  exact lt_irrefl 0 hpos
theorem x_dist_le_anchor (F : V2AnchorFrame S Z) {x : ℝ²} (hx : x ∈ A) :
    dist (F.T x) (F.T S.Packet.center) ≤ dist (F.T S.triangle.v2) (F.T S.Packet.center) := by
  have hX := F.hdisk x hx
  have hv2sq := F.hv2_on_mec
  have h : dist (F.T x) (F.T S.Packet.center) ^ 2
      ≤ dist (F.T S.triangle.v2) (F.T S.Packet.center) ^ 2 := by
    rw [hv2sq]; exact hX
  have hXnn : (0 : ℝ) ≤ dist (F.T x) (F.T S.Packet.center) := dist_nonneg
  have hv2nn : (0 : ℝ) ≤ dist (F.T S.triangle.v2) (F.T S.Packet.center) := dist_nonneg
  nlinarith only [hX, hv2sq, hv2nn, h, hXnn]
theorem a2_x_le_two (F : V2AnchorFrame S Z) : (F.T Z.a2) 0 ≤ 2 := by
  have h := F.hcirc_a2
  have hsq : dist (F.T S.triangle.v2) (F.T Z.a2) ^ 2 = 1 := by rw [h]; norm_num
  rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, F.hv2, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1] at hsq
  nlinarith only [hsq, sq_nonneg ((F.T Z.a2) 1)]
theorem circ_disk_x_floor (F : V2AnchorFrame S Z) {p : ℝ²}
    (hpA : p ∈ A) (hp_circ : dist (F.T S.triangle.v2) (F.T p) = 1) :
    (F.T p) 0 ≤ 2 * F.Oy * (F.T p) 1 := by
  have hunit : ((F.T p) 0 - 1) ^ 2 + (F.T p) 1 ^ 2 = 1 := by
    have h : dist (F.T S.triangle.v2) (F.T p) ^ 2 = 1 := by rw [hp_circ]; norm_num
    rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, F.hv2, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1] at h
    nlinarith only [h]
  have hdisk := F.hdisk p hpA
  rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, F.hO, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1] at hdisk
  nlinarith only [hunit, hdisk]
theorem bisectorKill_args_v1a2 (F : V2AnchorFrame S Z) {x : ℝ²}
    (hxA : x ∈ A) (hxy : (F.T x) 1 ≤ 0) (hxne : x ≠ S.triangle.v2) :
    dist (F.T x) (F.T S.Packet.center) ≤ dist (F.T S.triangle.v2) (F.T S.Packet.center) ∧
    dist (F.T S.triangle.v2) (F.T S.triangle.v1) = dist (F.T S.triangle.v2) (F.T Z.a2) ∧
    (F.T S.triangle.v2) 1 = 0 ∧
    (F.T x) 1 ≤ 0 ∧
    0 < ((F.T S.triangle.v1) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.a2) 1 - (F.T S.triangle.v2) 1) ∧
    (((F.T S.triangle.v1) 0 - (F.T S.triangle.v2) 0)
        + ((F.T Z.a2) 0 - (F.T S.triangle.v2) 0))
        * ((F.T S.triangle.v2) 0 - (F.T S.Packet.center) 0)
      + (((F.T S.triangle.v1) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.a2) 1 - (F.T S.triangle.v2) 1))
        * ((F.T S.triangle.v2) 1 - (F.T S.Packet.center) 1)
        < 0 ∧
    F.T S.triangle.v1 ≠ F.T Z.a2 ∧
    F.T x ≠ F.T S.triangle.v2 := by
  have hv1c0 : (F.T S.triangle.v1) 0 = 0 := by rw [F.hv1, b3n9m060_vec2_coord0]
  have hv1c1 : (F.T S.triangle.v1) 1 = 0 := by rw [F.hv1, b3n9m060_vec2_coord1]
  have hv2c0 : (F.T S.triangle.v2) 0 = 1 := by rw [F.hv2, b3n9m060_vec2_coord0]
  have hv2c1 : (F.T S.triangle.v2) 1 = 0 := by rw [F.hv2, b3n9m060_vec2_coord1]
  have hOc0 : (F.T S.Packet.center) 0 = 1 / 2 := by rw [F.hO, b3n9m060_vec2_coord0]
  have hOc1 : (F.T S.Packet.center) 1 = F.Oy := by rw [F.hO, b3n9m060_vec2_coord1]
  have ha2x : (F.T Z.a2) 0 ≤ 2 := F.a2_x_le_two
  have ha2y : 0 < (F.T Z.a2) 1 := F.ha2_y
  have hOy : 0 < F.Oy := F.hOy_pos
  refine ⟨F.x_dist_le_anchor hxA, ?_, hv2c1, hxy, ?_, ?_, ?_, ?_⟩
  · rw [F.hcirc_v1, F.hcirc_a2]
  · rw [hv1c1, hv2c1]; linarith [ha2y]
  · rw [hv1c0, hv1c1, hv2c0, hv2c1, hOc0, hOc1]
    nlinarith only [ha2x, ha2y, hOy]
  ·
    intro heq
    have hcontr : (F.T S.triangle.v1) 1 = (F.T Z.a2) 1 := by rw [heq]
    rw [hv1c1] at hcontr
    linarith [ha2y, hcontr]
  ·
    intro heq
    exact hxne (F.T_injective heq)
theorem bisectorKill_args_v3a2 (F : V2AnchorFrame S Z) {x : ℝ²}
    (hxA : x ∈ A) (hxy : (F.T x) 1 ≤ 0) (hxne : x ≠ S.triangle.v2) :
    dist (F.T x) (F.T S.Packet.center) ≤ dist (F.T S.triangle.v2) (F.T S.Packet.center) ∧
    dist (F.T S.triangle.v2) (F.T S.triangle.v3) = dist (F.T S.triangle.v2) (F.T Z.a2) ∧
    (F.T S.triangle.v2) 1 = 0 ∧
    (F.T x) 1 ≤ 0 ∧
    0 < ((F.T S.triangle.v3) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.a2) 1 - (F.T S.triangle.v2) 1) ∧
    (((F.T S.triangle.v3) 0 - (F.T S.triangle.v2) 0)
        + ((F.T Z.a2) 0 - (F.T S.triangle.v2) 0))
        * ((F.T S.triangle.v2) 0 - (F.T S.Packet.center) 0)
      + (((F.T S.triangle.v3) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.a2) 1 - (F.T S.triangle.v2) 1))
        * ((F.T S.triangle.v2) 1 - (F.T S.Packet.center) 1)
        < 0 ∧
    F.T S.triangle.v3 ≠ F.T Z.a2 ∧
    F.T x ≠ F.T S.triangle.v2 := by
  have hv2c0 : (F.T S.triangle.v2) 0 = 1 := by rw [F.hv2, b3n9m060_vec2_coord0]
  have hv2c1 : (F.T S.triangle.v2) 1 = 0 := by rw [F.hv2, b3n9m060_vec2_coord1]
  have hv3c0 : (F.T S.triangle.v3) 0 = 1 + F.c := by rw [F.hv3, b3n9m060_vec2_coord0]
  have hv3c1 : (F.T S.triangle.v3) 1 = F.sg := by rw [F.hv3, b3n9m060_vec2_coord1]
  have hOc0 : (F.T S.Packet.center) 0 = 1 / 2 := by rw [F.hO, b3n9m060_vec2_coord0]
  have hOc1 : (F.T S.Packet.center) 1 = F.Oy := by rw [F.hO, b3n9m060_vec2_coord1]
  have ha2x : (F.T Z.a2) 0 ≤ 2 := F.a2_x_le_two
  have ha2y : 0 < (F.T Z.a2) 1 := F.ha2_y
  have hOy : 0 < F.Oy := F.hOy_pos
  have hsg : 0 < F.sg := F.hsg_pos
  have hmec : 2 * F.sg * F.Oy = 1 + F.c := F.hmec
  refine ⟨F.x_dist_le_anchor hxA, ?_, hv2c1, hxy, ?_, ?_, ?_, ?_⟩
  · rw [F.hcirc_v3, F.hcirc_a2]
  · rw [hv3c1, hv2c1]; linarith [hsg, ha2y]
  · rw [hv3c0, hv3c1, hv2c0, hv2c1, hOc0, hOc1]
    nlinarith only [ha2x, hmec, ha2y, hOy]
  ·
    intro heq
    have ha2I2 : Z.a2 ∈ S.I2 := by rw [Z.hI2]; simp
    have hne : S.triangle.v3 ≠ Z.a2 :=
      fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp ha2I2).2).1 h.symm
    exact hne (F.T_injective heq)
  · intro heq
    exact hxne (F.T_injective heq)
theorem bisectorKill_args_v1b2 (F : V2AnchorFrame S Z) {x : ℝ²}
    (hxA : x ∈ A) (hxy : (F.T x) 1 ≤ 0) (hxne : x ≠ S.triangle.v2) :
    dist (F.T x) (F.T S.Packet.center) ≤ dist (F.T S.triangle.v2) (F.T S.Packet.center) ∧
    dist (F.T S.triangle.v2) (F.T S.triangle.v1) = dist (F.T S.triangle.v2) (F.T Z.b2) ∧
    (F.T S.triangle.v2) 1 = 0 ∧
    (F.T x) 1 ≤ 0 ∧
    0 < ((F.T S.triangle.v1) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.b2) 1 - (F.T S.triangle.v2) 1) ∧
    (((F.T S.triangle.v1) 0 - (F.T S.triangle.v2) 0)
        + ((F.T Z.b2) 0 - (F.T S.triangle.v2) 0))
        * ((F.T S.triangle.v2) 0 - (F.T S.Packet.center) 0)
      + (((F.T S.triangle.v1) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.b2) 1 - (F.T S.triangle.v2) 1))
        * ((F.T S.triangle.v2) 1 - (F.T S.Packet.center) 1)
        < 0 ∧
    F.T S.triangle.v1 ≠ F.T Z.b2 ∧
    F.T x ≠ F.T S.triangle.v2 := by
  have hv1c1 : (F.T S.triangle.v1) 1 = 0 := by rw [F.hv1, b3n9m060_vec2_coord1]
  have hv2c0 : (F.T S.triangle.v2) 0 = 1 := by rw [F.hv2, b3n9m060_vec2_coord0]
  have hv2c1 : (F.T S.triangle.v2) 1 = 0 := by rw [F.hv2, b3n9m060_vec2_coord1]
  have hOc0 : (F.T S.Packet.center) 0 = 1 / 2 := by rw [F.hO, b3n9m060_vec2_coord0]
  have hOc1 : (F.T S.Packet.center) 1 = F.Oy := by rw [F.hO, b3n9m060_vec2_coord1]
  have hb2y : 0 < (F.T Z.b2) 1 := F.hb2_y
  have hv1floor : (F.T S.triangle.v1) 0 ≤ 2 * F.Oy * (F.T S.triangle.v1) 1 :=
    F.circ_disk_x_floor (S.b3n9m060_v1_mem_A) F.hcirc_v1
  have hb2floor : (F.T Z.b2) 0 ≤ 2 * F.Oy * (F.T Z.b2) 1 :=
    F.circ_disk_x_floor (S.b3n9m060_b2_mem_A Z) F.hcirc_b2
  refine ⟨F.x_dist_le_anchor hxA, ?_, hv2c1, hxy, ?_, ?_, ?_, ?_⟩
  · rw [F.hcirc_v1, F.hcirc_b2]
  · rw [hv1c1, hv2c1]; linarith [hb2y]
  · rw [hv2c0, hv2c1, hOc0, hOc1]
    nlinarith only [hv1floor, hb2floor, hv1c1]
  ·
    intro heq
    have hcontr : (F.T S.triangle.v1) 1 = (F.T Z.b2) 1 := by rw [heq]
    rw [hv1c1] at hcontr
    linarith [hb2y, hcontr]
  · intro heq
    exact hxne (F.T_injective heq)
theorem bisectorKill_args_v3b2 (F : V2AnchorFrame S Z) {x : ℝ²}
    (hxA : x ∈ A) (hxy : (F.T x) 1 ≤ 0) (hxne : x ≠ S.triangle.v2) :
    dist (F.T x) (F.T S.Packet.center) ≤ dist (F.T S.triangle.v2) (F.T S.Packet.center) ∧
    dist (F.T S.triangle.v2) (F.T S.triangle.v3) = dist (F.T S.triangle.v2) (F.T Z.b2) ∧
    (F.T S.triangle.v2) 1 = 0 ∧
    (F.T x) 1 ≤ 0 ∧
    0 < ((F.T S.triangle.v3) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.b2) 1 - (F.T S.triangle.v2) 1) ∧
    (((F.T S.triangle.v3) 0 - (F.T S.triangle.v2) 0)
        + ((F.T Z.b2) 0 - (F.T S.triangle.v2) 0))
        * ((F.T S.triangle.v2) 0 - (F.T S.Packet.center) 0)
      + (((F.T S.triangle.v3) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.b2) 1 - (F.T S.triangle.v2) 1))
        * ((F.T S.triangle.v2) 1 - (F.T S.Packet.center) 1)
        < 0 ∧
    F.T S.triangle.v3 ≠ F.T Z.b2 ∧
    F.T x ≠ F.T S.triangle.v2 := by
  have hv2c0 : (F.T S.triangle.v2) 0 = 1 := by rw [F.hv2, b3n9m060_vec2_coord0]
  have hv2c1 : (F.T S.triangle.v2) 1 = 0 := by rw [F.hv2, b3n9m060_vec2_coord1]
  have hv3c1 : (F.T S.triangle.v3) 1 = F.sg := by rw [F.hv3, b3n9m060_vec2_coord1]
  have hOc0 : (F.T S.Packet.center) 0 = 1 / 2 := by rw [F.hO, b3n9m060_vec2_coord0]
  have hOc1 : (F.T S.Packet.center) 1 = F.Oy := by rw [F.hO, b3n9m060_vec2_coord1]
  have hb2y : 0 < (F.T Z.b2) 1 := F.hb2_y
  have hsg : 0 < F.sg := F.hsg_pos
  have hv3floor : (F.T S.triangle.v3) 0 ≤ 2 * F.Oy * (F.T S.triangle.v3) 1 :=
    F.circ_disk_x_floor (S.b3n9m060_v3_mem_A) F.hcirc_v3
  have hb2floor : (F.T Z.b2) 0 ≤ 2 * F.Oy * (F.T Z.b2) 1 :=
    F.circ_disk_x_floor (S.b3n9m060_b2_mem_A Z) F.hcirc_b2
  refine ⟨F.x_dist_le_anchor hxA, ?_, hv2c1, hxy, ?_, ?_, ?_, ?_⟩
  · rw [F.hcirc_v3, F.hcirc_b2]
  · rw [hv3c1, hv2c1]; linarith [hsg, hb2y]
  · rw [hv2c0, hv2c1, hOc0, hOc1]
    nlinarith only [hv3floor, hb2floor]
  ·
    intro heq
    have hb2I2 : Z.b2 ∈ S.I2 := by rw [Z.hI2]; simp
    have hne : S.triangle.v3 ≠ Z.b2 :=
      fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hb2I2).2).1 h.symm
    exact hne (F.T_injective heq)
  · intro heq
    exact hxne (F.T_injective heq)
theorem bisectorKill_args_a2b2 (F : V2AnchorFrame S Z) {x : ℝ²}
    (hxA : x ∈ A) (hxy : (F.T x) 1 ≤ 0) (hxne : x ≠ S.triangle.v2) :
    dist (F.T x) (F.T S.Packet.center) ≤ dist (F.T S.triangle.v2) (F.T S.Packet.center) ∧
    dist (F.T S.triangle.v2) (F.T Z.a2) = dist (F.T S.triangle.v2) (F.T Z.b2) ∧
    (F.T S.triangle.v2) 1 = 0 ∧
    (F.T x) 1 ≤ 0 ∧
    0 < ((F.T Z.a2) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.b2) 1 - (F.T S.triangle.v2) 1) ∧
    (((F.T Z.a2) 0 - (F.T S.triangle.v2) 0)
        + ((F.T Z.b2) 0 - (F.T S.triangle.v2) 0))
        * ((F.T S.triangle.v2) 0 - (F.T S.Packet.center) 0)
      + (((F.T Z.a2) 1 - (F.T S.triangle.v2) 1)
        + ((F.T Z.b2) 1 - (F.T S.triangle.v2) 1))
        * ((F.T S.triangle.v2) 1 - (F.T S.Packet.center) 1)
        < 0 ∧
    F.T Z.a2 ≠ F.T Z.b2 ∧
    F.T x ≠ F.T S.triangle.v2 := by
  have hv2c0 : (F.T S.triangle.v2) 0 = 1 := by rw [F.hv2, b3n9m060_vec2_coord0]
  have hv2c1 : (F.T S.triangle.v2) 1 = 0 := by rw [F.hv2, b3n9m060_vec2_coord1]
  have hOc0 : (F.T S.Packet.center) 0 = 1 / 2 := by rw [F.hO, b3n9m060_vec2_coord0]
  have hOc1 : (F.T S.Packet.center) 1 = F.Oy := by rw [F.hO, b3n9m060_vec2_coord1]
  have ha2y : 0 < (F.T Z.a2) 1 := F.ha2_y
  have hb2y : 0 < (F.T Z.b2) 1 := F.hb2_y
  have ha2floor : (F.T Z.a2) 0 ≤ 2 * F.Oy * (F.T Z.a2) 1 :=
    F.circ_disk_x_floor (S.b3n9m060_a2_mem_A Z) F.hcirc_a2
  have hb2floor : (F.T Z.b2) 0 ≤ 2 * F.Oy * (F.T Z.b2) 1 :=
    F.circ_disk_x_floor (S.b3n9m060_b2_mem_A Z) F.hcirc_b2
  refine ⟨F.x_dist_le_anchor hxA, ?_, hv2c1, hxy, ?_, ?_, ?_, ?_⟩
  · rw [F.hcirc_a2, F.hcirc_b2]
  · rw [hv2c1]; linarith [ha2y, hb2y]
  · rw [hv2c0, hv2c1, hOc0, hOc1]
    nlinarith only [ha2floor, hb2floor]
  ·
    intro heq
    have ha2_ne_b2 : Z.a2 ≠ Z.b2 := by
      have hI2card : ({Z.a2, Z.b2} : Finset ℝ²).card = 2 := by
        simpa [Z.hI2] using (p2mCoreSupport S).I2_card_eq_two
      intro h; simp [h] at hI2card
    exact ha2_ne_b2 (F.T_injective heq)
  · intro heq
    exact hxne (F.T_injective heq)
theorem bisectorKill_args_v1v3 (F : V2AnchorFrame S Z) {x : ℝ²}
    (hxA : x ∈ A) (hxy : (F.T x) 1 ≤ 0) (hxne : x ≠ S.triangle.v2) :
    dist (F.T x) (F.T S.Packet.center) ≤ dist (F.T S.triangle.v2) (F.T S.Packet.center) ∧
    dist (F.T S.triangle.v2) (F.T S.triangle.v1) = dist (F.T S.triangle.v2) (F.T S.triangle.v3) ∧
    (F.T S.triangle.v2) 1 = 0 ∧
    (F.T x) 1 ≤ 0 ∧
    0 < ((F.T S.triangle.v1) 1 - (F.T S.triangle.v2) 1)
        + ((F.T S.triangle.v3) 1 - (F.T S.triangle.v2) 1) ∧
    (((F.T S.triangle.v1) 0 - (F.T S.triangle.v2) 0)
        + ((F.T S.triangle.v3) 0 - (F.T S.triangle.v2) 0))
        * ((F.T S.triangle.v2) 0 - (F.T S.Packet.center) 0)
      + (((F.T S.triangle.v1) 1 - (F.T S.triangle.v2) 1)
        + ((F.T S.triangle.v3) 1 - (F.T S.triangle.v2) 1))
        * ((F.T S.triangle.v2) 1 - (F.T S.Packet.center) 1)
        < 0 ∧
    F.T S.triangle.v1 ≠ F.T S.triangle.v3 ∧
    F.T x ≠ F.T S.triangle.v2 := by
  have hv1c1 : (F.T S.triangle.v1) 1 = 0 := by rw [F.hv1, b3n9m060_vec2_coord1]
  have hv2c0 : (F.T S.triangle.v2) 0 = 1 := by rw [F.hv2, b3n9m060_vec2_coord0]
  have hv2c1 : (F.T S.triangle.v2) 1 = 0 := by rw [F.hv2, b3n9m060_vec2_coord1]
  have hv3c1 : (F.T S.triangle.v3) 1 = F.sg := by rw [F.hv3, b3n9m060_vec2_coord1]
  have hOc0 : (F.T S.Packet.center) 0 = 1 / 2 := by rw [F.hO, b3n9m060_vec2_coord0]
  have hOc1 : (F.T S.Packet.center) 1 = F.Oy := by rw [F.hO, b3n9m060_vec2_coord1]
  have hsg : 0 < F.sg := F.hsg_pos
  have hv1floor : (F.T S.triangle.v1) 0 ≤ 2 * F.Oy * (F.T S.triangle.v1) 1 :=
    F.circ_disk_x_floor (S.b3n9m060_v1_mem_A) F.hcirc_v1
  have hv3floor : (F.T S.triangle.v3) 0 ≤ 2 * F.Oy * (F.T S.triangle.v3) 1 :=
    F.circ_disk_x_floor (S.b3n9m060_v3_mem_A) F.hcirc_v3
  refine ⟨F.x_dist_le_anchor hxA, ?_, hv2c1, hxy, ?_, ?_, ?_, ?_⟩
  · rw [F.hcirc_v1, F.hcirc_v3]
  · rw [hv1c1, hv2c1]; linarith [hsg, hv3c1]
  · rw [hv2c0, hv2c1, hOc0, hOc1]
    nlinarith only [hv1floor, hv3floor, hv1c1]
  ·
    intro heq
    exact S.triangle.v13_ne (F.T_injective heq)
  · intro heq
    exact hxne (F.T_injective heq)
end V2AnchorFrame
theorem b3n9m060_frame_c1_upper
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {p : ℝ²}
    {T : ℝ² → ℝ²} (tau : Problem97.CGN.SimilarityTransportData T)
    (hv1 : T S.triangle.v1 = Problem97.CGN.vec2 0 0)
    (hv2 : T S.triangle.v2 = Problem97.CGN.vec2 1 0)
    (hsg_pos : 0 < (T S.triangle.v3) 1)
    (hpI1 : p ∈ S.I1) :
    0 < (T p) 1 := by
  have hside := S.c1_vertex_same_open_side_as_v3 hpI1
  have hy := b3n9m060_chart_y_product (T := T) tau (p := p) (q := S.triangle.v3) hv1 hv2
  have hpos : 0 < (T p) 1 * (T S.triangle.v3) 1 := by
    rw [hy]; exact mul_pos (pow_pos tau.scale_pos 4) hside
  nlinarith only [hpos, hsg_pos]
structure V1AnchorFrame {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) where
  base : V2AnchorFrame S Z
  ha1A : Z.a1 ∈ A
  hb1A : Z.b1 ∈ A
  hcirc_a1 : dist (base.T S.triangle.v1) (base.T Z.a1) = 1
  hcirc_b1 : dist (base.T S.triangle.v1) (base.T Z.b1) = 1
  hcirc_v2 : dist (base.T S.triangle.v1) (base.T S.triangle.v2) = 1
  ha1_y : 0 < (base.T Z.a1) 1
  hb1_y : 0 < (base.T Z.b1) 1
noncomputable def v1AnchorFrame_of_hexact
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S)
    {r s : ℝ}
    (hC3pin : S.witnessClassAt_v1 r ∩ S.CP.C3 = ({S.triangle.v2} : Finset ℝ²))
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    V1AnchorFrame S Z := by
  classical
  let base := S.v2AnchorFrame_of_hexact Z hexact
  have hv2_in : S.triangle.v2 ∈ S.witnessClassAt_v1 r := by
    have hmem : S.triangle.v2 ∈ S.witnessClassAt_v1 r ∩ S.CP.C3 := by
      rw [hC3pin]; simp
    exact (Finset.mem_inter.mp hmem).1
  have hv1v2 : dist S.triangle.v1 S.triangle.v2 = r :=
    (Finset.mem_filter.mp hv2_in).2
  have hr : 0 < r := by
    rw [← hv1v2]; exact dist_pos.mpr S.triangle.v12_ne
  have hcore := (p2mCoreSupport S).coreSelector_v1 hr hcard
  have hI1sub : S.I1 ⊆ S.witnessClassAt_v1 r := hcore.2.1
  have ha1I1 : Z.a1 ∈ S.I1 := by rw [Z.hI1]; simp
  have hb1I1 : Z.b1 ∈ S.I1 := by rw [Z.hI1]; simp
  have ha1_in : Z.a1 ∈ S.witnessClassAt_v1 r := hI1sub ha1I1
  have hb1_in : Z.b1 ∈ S.witnessClassAt_v1 r := hI1sub hb1I1
  have ha1A : Z.a1 ∈ A := (Finset.mem_filter.mp ha1_in).1
  have hb1A : Z.b1 ∈ A := (Finset.mem_filter.mp hb1_in).1
  have hv1a1 : dist S.triangle.v1 Z.a1 = r := (Finset.mem_filter.mp ha1_in).2
  have hv1b1 : dist S.triangle.v1 Z.b1 = r := (Finset.mem_filter.mp hb1_in).2
  have hscale : base.tau.scale * r = 1 := by
    have hbase : dist (base.T S.triangle.v1) (base.T S.triangle.v2)
        = base.tau.scale * r := by
      rw [base.tau.dist_image, hv1v2]
    have hone : dist (base.T S.triangle.v1) (base.T S.triangle.v2) = 1 := by
      rw [base.hv1, base.hv2, b3n9m060_dist_vec2_00_10]
    rw [← hbase, hone]
  have hcirc_a1 : dist (base.T S.triangle.v1) (base.T Z.a1) = 1 := by
    rw [base.tau.dist_image, hv1a1, hscale]
  have hcirc_b1 : dist (base.T S.triangle.v1) (base.T Z.b1) = 1 := by
    rw [base.tau.dist_image, hv1b1, hscale]
  have hcirc_v2 : dist (base.T S.triangle.v1) (base.T S.triangle.v2) = 1 := by
    rw [base.tau.dist_image, hv1v2, hscale]
  have hsg_pos : 0 < (base.T S.triangle.v3) 1 := by rw [base.hv3, b3n9m060_vec2_coord1]; exact base.hsg_pos
  have ha1_y : 0 < (base.T Z.a1) 1 :=
    S.b3n9m060_frame_c1_upper base.tau base.hv1 base.hv2 hsg_pos ha1I1
  have hb1_y : 0 < (base.T Z.b1) 1 :=
    S.b3n9m060_frame_c1_upper base.tau base.hv1 base.hv2 hsg_pos hb1I1
  exact
    { base := base
      ha1A := ha1A
      hb1A := hb1A
      hcirc_a1 := hcirc_a1
      hcirc_b1 := hcirc_b1
      hcirc_v2 := hcirc_v2
      ha1_y := ha1_y
      hb1_y := hb1_y }
namespace V1AnchorFrame
variable {A : Finset ℝ²} {S : FiniteEndpointShell A} {Z : ZeroDefectCapLayout S}
theorem x_dist_le_anchor (F : V1AnchorFrame S Z) {x : ℝ²} (hx : x ∈ A) :
    dist (F.base.T x) (F.base.T S.Packet.center)
      ≤ dist (F.base.T S.triangle.v1) (F.base.T S.Packet.center) := by
  have hX := F.base.hdisk x hx
  have hv1_on_mec : dist (F.base.T S.triangle.v1) (F.base.T S.Packet.center) ^ 2
      = 1 / 4 + F.base.Oy ^ 2 := by
    rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, F.base.hv1, F.base.hO,
      b3n9m060_vec2_coord0, b3n9m060_vec2_coord1, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1]
    ring
  have h : dist (F.base.T x) (F.base.T S.Packet.center) ^ 2
      ≤ dist (F.base.T S.triangle.v1) (F.base.T S.Packet.center) ^ 2 := by
    rw [hv1_on_mec]; exact hX
  have hXnn : (0 : ℝ) ≤ dist (F.base.T x) (F.base.T S.Packet.center) := dist_nonneg
  have hv1nn : (0 : ℝ) ≤ dist (F.base.T S.triangle.v1) (F.base.T S.Packet.center) := dist_nonneg
  nlinarith only [hX, hv1_on_mec, hv1nn, h, hXnn]
theorem circ_disk_x_floor (F : V1AnchorFrame S Z) {p : ℝ²}
    (hpA : p ∈ A) (hp_circ : dist (F.base.T S.triangle.v1) (F.base.T p) = 1) :
    1 - 2 * F.base.Oy * (F.base.T p) 1 ≤ (F.base.T p) 0 := by
  have hunit : (F.base.T p) 0 ^ 2 + (F.base.T p) 1 ^ 2 = 1 := by
    have h : dist (F.base.T S.triangle.v1) (F.base.T p) ^ 2 = 1 := by rw [hp_circ]; norm_num
    rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, F.base.hv1, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1] at h
    nlinarith only [h]
  have hdisk := F.base.hdisk p hpA
  rw [b3n9m060_dist_sq_eq_coord_sq_add_coord_sq, F.base.hO, b3n9m060_vec2_coord0, b3n9m060_vec2_coord1] at hdisk
  nlinarith only [hunit, hdisk]
theorem T_injective (F : V1AnchorFrame S Z) : Function.Injective F.base.T :=
  F.base.T_injective
theorem bisectorKill_args_a1b1 (F : V1AnchorFrame S Z) {x : ℝ²}
    (hxA : x ∈ A) (hxy : (F.base.T x) 1 ≤ 0) (hxne : x ≠ S.triangle.v1) :
    dist (F.base.T x) (F.base.T S.Packet.center)
        ≤ dist (F.base.T S.triangle.v1) (F.base.T S.Packet.center) ∧
    dist (F.base.T S.triangle.v1) (F.base.T Z.a1)
        = dist (F.base.T S.triangle.v1) (F.base.T Z.b1) ∧
    (F.base.T S.triangle.v1) 1 = 0 ∧
    (F.base.T x) 1 ≤ 0 ∧
    0 < ((F.base.T Z.a1) 1 - (F.base.T S.triangle.v1) 1)
        + ((F.base.T Z.b1) 1 - (F.base.T S.triangle.v1) 1) ∧
    (((F.base.T Z.a1) 0 - (F.base.T S.triangle.v1) 0)
        + ((F.base.T Z.b1) 0 - (F.base.T S.triangle.v1) 0))
        * ((F.base.T S.triangle.v1) 0 - (F.base.T S.Packet.center) 0)
      + (((F.base.T Z.a1) 1 - (F.base.T S.triangle.v1) 1)
        + ((F.base.T Z.b1) 1 - (F.base.T S.triangle.v1) 1))
        * ((F.base.T S.triangle.v1) 1 - (F.base.T S.Packet.center) 1)
        < 0 ∧
    F.base.T Z.a1 ≠ F.base.T Z.b1 ∧
    F.base.T x ≠ F.base.T S.triangle.v1 := by
  have hv1c0 : (F.base.T S.triangle.v1) 0 = 0 := by rw [F.base.hv1, b3n9m060_vec2_coord0]
  have hv1c1 : (F.base.T S.triangle.v1) 1 = 0 := by rw [F.base.hv1, b3n9m060_vec2_coord1]
  have hOc0 : (F.base.T S.Packet.center) 0 = 1 / 2 := by rw [F.base.hO, b3n9m060_vec2_coord0]
  have hOc1 : (F.base.T S.Packet.center) 1 = F.base.Oy := by rw [F.base.hO, b3n9m060_vec2_coord1]
  have ha1y : 0 < (F.base.T Z.a1) 1 := F.ha1_y
  have hb1y : 0 < (F.base.T Z.b1) 1 := F.hb1_y
  have hOy : 0 < F.base.Oy := F.base.hOy_pos
  have ha1floor : 1 - 2 * F.base.Oy * (F.base.T Z.a1) 1 ≤ (F.base.T Z.a1) 0 :=
    F.circ_disk_x_floor F.ha1A F.hcirc_a1
  have hb1floor : 1 - 2 * F.base.Oy * (F.base.T Z.b1) 1 ≤ (F.base.T Z.b1) 0 :=
    F.circ_disk_x_floor F.hb1A F.hcirc_b1
  refine ⟨F.x_dist_le_anchor hxA, ?_, hv1c1, hxy, ?_, ?_, ?_, ?_⟩
  · rw [F.hcirc_a1, F.hcirc_b1]
  · rw [hv1c1]; linarith [ha1y, hb1y]
  · rw [hv1c0, hv1c1, hOc0, hOc1]
    nlinarith only [ha1floor, hb1floor, ha1y, hb1y, hOy]
  ·
    intro heq
    have ha1_ne_b1 : Z.a1 ≠ Z.b1 := by
      have hI1card : ({Z.a1, Z.b1} : Finset ℝ²).card = 2 := by
        simpa [Z.hI1] using (p2mCoreSupport S).I1_card_eq_two
      intro h; simp [h] at hI1card
    exact ha1_ne_b1 (F.T_injective heq)
  · intro heq
    exact hxne (F.T_injective heq)
theorem bisectorKill_args_v2a1 (F : V1AnchorFrame S Z) {x : ℝ²}
    (hxA : x ∈ A) (hxy : (F.base.T x) 1 ≤ 0) (hxne : x ≠ S.triangle.v1) :
    dist (F.base.T x) (F.base.T S.Packet.center)
        ≤ dist (F.base.T S.triangle.v1) (F.base.T S.Packet.center) ∧
    dist (F.base.T S.triangle.v1) (F.base.T S.triangle.v2)
        = dist (F.base.T S.triangle.v1) (F.base.T Z.a1) ∧
    (F.base.T S.triangle.v1) 1 = 0 ∧
    (F.base.T x) 1 ≤ 0 ∧
    0 < ((F.base.T S.triangle.v2) 1 - (F.base.T S.triangle.v1) 1)
        + ((F.base.T Z.a1) 1 - (F.base.T S.triangle.v1) 1) ∧
    (((F.base.T S.triangle.v2) 0 - (F.base.T S.triangle.v1) 0)
        + ((F.base.T Z.a1) 0 - (F.base.T S.triangle.v1) 0))
        * ((F.base.T S.triangle.v1) 0 - (F.base.T S.Packet.center) 0)
      + (((F.base.T S.triangle.v2) 1 - (F.base.T S.triangle.v1) 1)
        + ((F.base.T Z.a1) 1 - (F.base.T S.triangle.v1) 1))
        * ((F.base.T S.triangle.v1) 1 - (F.base.T S.Packet.center) 1)
        < 0 ∧
    F.base.T S.triangle.v2 ≠ F.base.T Z.a1 ∧
    F.base.T x ≠ F.base.T S.triangle.v1 := by
  have hv1c0 : (F.base.T S.triangle.v1) 0 = 0 := by rw [F.base.hv1, b3n9m060_vec2_coord0]
  have hv1c1 : (F.base.T S.triangle.v1) 1 = 0 := by rw [F.base.hv1, b3n9m060_vec2_coord1]
  have hv2c0 : (F.base.T S.triangle.v2) 0 = 1 := by rw [F.base.hv2, b3n9m060_vec2_coord0]
  have hv2c1 : (F.base.T S.triangle.v2) 1 = 0 := by rw [F.base.hv2, b3n9m060_vec2_coord1]
  have hOc0 : (F.base.T S.Packet.center) 0 = 1 / 2 := by rw [F.base.hO, b3n9m060_vec2_coord0]
  have hOc1 : (F.base.T S.Packet.center) 1 = F.base.Oy := by rw [F.base.hO, b3n9m060_vec2_coord1]
  have ha1y : 0 < (F.base.T Z.a1) 1 := F.ha1_y
  have hOy : 0 < F.base.Oy := F.base.hOy_pos
  have ha1floor : 1 - 2 * F.base.Oy * (F.base.T Z.a1) 1 ≤ (F.base.T Z.a1) 0 :=
    F.circ_disk_x_floor F.ha1A F.hcirc_a1
  refine ⟨F.x_dist_le_anchor hxA, ?_, hv1c1, hxy, ?_, ?_, ?_, ?_⟩
  · rw [F.hcirc_v2, F.hcirc_a1]
  · rw [hv1c1, hv2c1]; linarith [ha1y]
  · rw [hv1c0, hv1c1, hv2c0, hv2c1, hOc0, hOc1]
    nlinarith only [ha1floor, ha1y, hOy]
  ·
    intro heq
    have ha1_ne_v2 : Z.a1 ≠ S.triangle.v2 := by
      have ha1I1 : Z.a1 ∈ S.I1 := by rw [Z.hI1]; simp
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp ha1I1).2).1
    exact ha1_ne_v2 (F.T_injective heq.symm)
  · intro heq
    exact hxne (F.T_injective heq)
theorem bisectorKill_args_v2b1 (F : V1AnchorFrame S Z) {x : ℝ²}
    (hxA : x ∈ A) (hxy : (F.base.T x) 1 ≤ 0) (hxne : x ≠ S.triangle.v1) :
    dist (F.base.T x) (F.base.T S.Packet.center)
        ≤ dist (F.base.T S.triangle.v1) (F.base.T S.Packet.center) ∧
    dist (F.base.T S.triangle.v1) (F.base.T S.triangle.v2)
        = dist (F.base.T S.triangle.v1) (F.base.T Z.b1) ∧
    (F.base.T S.triangle.v1) 1 = 0 ∧
    (F.base.T x) 1 ≤ 0 ∧
    0 < ((F.base.T S.triangle.v2) 1 - (F.base.T S.triangle.v1) 1)
        + ((F.base.T Z.b1) 1 - (F.base.T S.triangle.v1) 1) ∧
    (((F.base.T S.triangle.v2) 0 - (F.base.T S.triangle.v1) 0)
        + ((F.base.T Z.b1) 0 - (F.base.T S.triangle.v1) 0))
        * ((F.base.T S.triangle.v1) 0 - (F.base.T S.Packet.center) 0)
      + (((F.base.T S.triangle.v2) 1 - (F.base.T S.triangle.v1) 1)
        + ((F.base.T Z.b1) 1 - (F.base.T S.triangle.v1) 1))
        * ((F.base.T S.triangle.v1) 1 - (F.base.T S.Packet.center) 1)
        < 0 ∧
    F.base.T S.triangle.v2 ≠ F.base.T Z.b1 ∧
    F.base.T x ≠ F.base.T S.triangle.v1 := by
  have hv1c0 : (F.base.T S.triangle.v1) 0 = 0 := by rw [F.base.hv1, b3n9m060_vec2_coord0]
  have hv1c1 : (F.base.T S.triangle.v1) 1 = 0 := by rw [F.base.hv1, b3n9m060_vec2_coord1]
  have hv2c0 : (F.base.T S.triangle.v2) 0 = 1 := by rw [F.base.hv2, b3n9m060_vec2_coord0]
  have hv2c1 : (F.base.T S.triangle.v2) 1 = 0 := by rw [F.base.hv2, b3n9m060_vec2_coord1]
  have hOc0 : (F.base.T S.Packet.center) 0 = 1 / 2 := by rw [F.base.hO, b3n9m060_vec2_coord0]
  have hOc1 : (F.base.T S.Packet.center) 1 = F.base.Oy := by rw [F.base.hO, b3n9m060_vec2_coord1]
  have hb1y : 0 < (F.base.T Z.b1) 1 := F.hb1_y
  have hOy : 0 < F.base.Oy := F.base.hOy_pos
  have hb1floor : 1 - 2 * F.base.Oy * (F.base.T Z.b1) 1 ≤ (F.base.T Z.b1) 0 :=
    F.circ_disk_x_floor F.hb1A F.hcirc_b1
  refine ⟨F.x_dist_le_anchor hxA, ?_, hv1c1, hxy, ?_, ?_, ?_, ?_⟩
  · rw [F.hcirc_v2, F.hcirc_b1]
  · rw [hv1c1, hv2c1]; linarith [hb1y]
  · rw [hv1c0, hv1c1, hv2c0, hv2c1, hOc0, hOc1]
    nlinarith only [hb1floor, hb1y, hOy]
  ·
    intro heq
    have hb1_ne_v2 : Z.b1 ≠ S.triangle.v2 := by
      have hb1I1 : Z.b1 ∈ S.I1 := by rw [Z.hI1]; simp
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hb1I1).2).1
    exact hb1_ne_v2 (F.T_injective heq.symm)
  · intro heq
    exact hxne (F.T_injective heq)
end V1AnchorFrame
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit060


section Batch3N9Unit051PeqB
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
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
    rw [hA, hB, b3n9m060_dist_sq_eq_coord_sq_add_coord_sq]
    simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
  have hAq_sq : dist A q ^ 2 = 1 + 2 * a + r ^ 2 := by
    rw [hA, hq, b3n9m060_dist_sq_eq_coord_sq_add_coord_sq]
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
  rcases (p2mCoreSupport S).exists_base_transportData q1 q2 hq1ne with
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
    rw [hv1Base, hv2Base, (p2mCoreSupport S).signedArea2_baseChord_vec2]
    linarith
  have build_from :
      ∀ {T0 : ℝ² → ℝ²},
        (tau0 : Problem97.CGN.SimilarityTransportData T0) →
        T0 q1 = Problem97.CGN.vec2 (-1) 0 →
        T0 q2 = Problem97.CGN.vec2 1 0 →
        0 < (T0 q3) 1 →
        ∃ r : ℝ, S.PEqBLowerApexConfig q r := by
    intro T0 tau0 hv1 hv2 hq3y_pos
    let T : ℝ² → ℝ² := fun x => b3n9m060_halfShift (T0 x)
    let tau : Problem97.CGN.SimilarityTransportData T :=
      b3n9m060_similarityTransportComp tau0 b3n9m060_halfShiftSimilarityTransportData
    have hv1T : T q1 = Problem97.CGN.vec2 0 0 := by
      dsimp [T]; rw [hv1]
      ext i <;> fin_cases i <;>
        simp [b3n9m060_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2T : T q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [T]; rw [hv2]
      ext i <;> fin_cases i <;>
        simp [b3n9m060_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3y_T : 0 < (T q3) 1 := by
      dsimp [T]
      simp only [b3n9m060_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
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
        rw [hv1, hv2, (p2mCoreSupport S).signedArea2_baseChord_vec2]; linarith
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
      rw [hv1, hv2, (p2mCoreSupport S).signedArea2_baseChord_vec2] at hq_img_lt
      dsimp [T]
      simp only [b3n9m060_halfShift, Problem97.CGN.vec2, EuclideanSpace.single_apply]
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
      have hsq := b3n9m060_dist_sq_eq_coord_sq_add_coord_sq (T q2) (T q3)
      rw [hBD_T, hv2c0, hv2c1] at hsq
      rw [hdx_def, hdy_def]; nlinarith only [hsq]
    have hcircQ : a ^ 2 + b ^ 2 = r ^ 2 := by
      have hsq := b3n9m060_dist_sq_eq_coord_sq_add_coord_sq (T q2) (T q)
      rw [hBq_T, hv2c0, hv2c1] at hsq
      rw [ha_def, hb_def]; nlinarith only [hsq]
    have hdot_raw : a * dx + b * dy = r ^ 2 / 2 := by
      have hsq := b3n9m060_dist_sq_eq_coord_sq_add_coord_sq (T q3) (T q)
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
      have hAD_sq := b3n9m060_dist_sq_eq_coord_sq_add_coord_sq (T q1) (T q3)
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
  · let Tflip : ℝ² → ℝ² := fun x => b3n9m060_flipY (Tbase x)
    let tauFlip : Problem97.CGN.SimilarityTransportData Tflip :=
      b3n9m060_similarityTransportComp tauBase b3n9m060_flipYSimilarityTransportData
    have hv1Flip : Tflip q1 = Problem97.CGN.vec2 (-1) 0 := by
      dsimp [Tflip]; rw [hv1Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hv2Flip : Tflip q2 = Problem97.CGN.vec2 1 0 := by
      dsimp [Tflip]; rw [hv2Base]
      ext i <;> fin_cases i <;>
        simp [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
    have hq3Flip : 0 < (Tflip q3) 1 := by
      dsimp [Tflip]
      simp only [b3n9m060_flipY, Problem97.CGN.vec2, EuclideanSpace.single_apply]
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

end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit051PeqB
-- Original module: Solutions.Batch3N9.N4d.FormBLowerForcesV3
section Batch3N9Unit055
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
set_option maxHeartbeats 2000000 in
theorem sharedCirclePointForcesV3_of_formB_lower
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hs : 0 < s)
    (hB : S.IsFormB_v1 r)
    (hA2 : (Z.a2 : ℝ²) ∈ S.I2)
    (h_a2eq : S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²))
    (hI2sub : S.I2 ⊆ S.witnessClassAt_v2 s) :
    S.SharedCirclePointForcesV3 Z r s := by
  classical
  obtain ⟨-, -, -, h_v2eq⟩ := hB
  intro q hqnamed hqT2 hqT1
  by_cases hqv3 : q = S.triangle.v3
  · exact hqv3
  exfalso
  have hqI1 : q ∈ S.I1 := by
    rw [Z.hI1]
    rcases Finset.mem_insert.mp hqnamed with h | hrest
    · simp [h]
    · rcases Finset.mem_insert.mp hrest with h | h
      · simp [h]
      · exact absurd (by simpa using h) hqv3
  let q1 : ℝ² := S.triangle.v1
  let q2 : ℝ² := S.triangle.v2
  let a : ℝ² := Z.a2
  let center : ℝ² := S.Packet.center
  have hqA : q ∈ A := (Finset.mem_filter.mp hqT1).1
  have haC2 : a ∈ S.CP.C2 := by
    unfold Problem97.FiniteEndpointShell.I2 at hA2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).2
  have haA : a ∈ A := S.CP.C2_subset haC2
  have haT1 : a ∈ S.witnessClassAt_v1 r := by
    have hamem : a ∈ ({a} : Finset ℝ²) := by simp
    rw [← h_a2eq] at hamem
    exact (Finset.mem_inter.mp hamem).1
  have haT2 : a ∈ S.witnessClassAt_v2 s := hI2sub hA2
  have hv2T1 : q2 ∈ S.witnessClassAt_v1 r := by
    have hv2mem : q2 ∈ ({q2} : Finset ℝ²) := by simp [q2]
    rw [← h_v2eq] at hv2mem
    exact (Finset.mem_inter.mp hv2mem).1
  have hr_q1q2 : dist q1 q2 = r := by
    simpa [q1, q2] using (Finset.mem_filter.mp hv2T1).2
  have hr_q1a : dist q1 a = r := by
    simpa [q1, a] using (Finset.mem_filter.mp haT1).2
  have hr_q1q : dist q1 q = r := by
    simpa [q1] using (Finset.mem_filter.mp hqT1).2
  have hs_q2a : dist q2 a = s := by
    simpa [q2, a] using (Finset.mem_filter.mp haT2).2
  have hs_q2q : dist q2 q = s := by
    simpa [q2] using (Finset.mem_filter.mp hqT2).2
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
    simp [nvec]
  have hβu : β.repr u = Finsupp.single 0 (1 : ℝ) := by
    simpa [β, nvec] using (β.repr_self 0)
  have horth : inner ℝ u nvec = 0 := by
    simp [nvec]
  have hq1mid : q1 - M = (-(1 / 2 : ℝ)) • u := by
    calc
      q1 - M = (1 / 2 : ℝ) • (q1 - q2) := by
        simp [M]
      _ = (-(1 / 2 : ℝ)) • u := by
        rw [show q1 - q2 = -u by
          dsimp [u]
          abel_nf]
        simp [smul_neg]
  have hq2mid : q2 - M = (1 / 2 : ℝ) • u := by
    simp [M, u]
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
  have hdist_sq_coeff :
      ∀ a b : ℝ, ‖a • u + b • nvec‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u‖ ^ 2 := by
    intro a b
    have horth' : inner ℝ (a • u) (b • nvec) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth]
      ring
    have hnorm :
        ‖a • u + b • nvec‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • nvec‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • u) (b • nvec) horth'
    have hu_part : ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
      calc
        ‖a • u‖ ^ 2 = (|a| * ‖u‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs]
        _ = |a| ^ 2 * ‖u‖ ^ 2 := by ring
        _ = a ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
    have hn_part : ‖b • nvec‖ ^ 2 = b ^ 2 * ‖u‖ ^ 2 := by
      calc
        ‖b • nvec‖ ^ 2 = (|b| * ‖u‖) ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, hnorm_nvec]
        _ = |b| ^ 2 * ‖u‖ ^ 2 := by ring
        _ = b ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
    rw [hnorm, hu_part, hn_part]
    ring
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
      have hsqpos : 0 < ‖u‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
      nlinarith only [hcenter_perp, hinner, hsqpos]
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
  have hdist_q1_sq :
      ∀ z : ℝ², dist q1 z ^ 2 = ((X z + 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 := by
    intro z
    rw [dist_comm, dist_eq_norm, hpt_minus_q1, hdist_sq_coeff]
  have hdist_q2_sq :
      ∀ z : ℝ², dist q2 z ^ 2 = ((X z - 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 := by
    intro z
    rw [dist_comm, dist_eq_norm, hpt_minus_q2, hdist_sq_coeff]
  have hdist_center_sq :
      ∀ z : ℝ², dist center z ^ 2 = (X z ^ 2 + (Y z - yc) ^ 2) * ‖u‖ ^ 2 := by
    intro z
    rw [dist_comm, dist_eq_norm, hpt_minus_center, hdist_sq_coeff]
  have hu_sq_pos : 0 < ‖u‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
  have hs_sq_pos : 0 < s ^ 2 := by positivity
  have hnorm_u : ‖u‖ = r := by
    rw [← hr_q1q2, dist_eq_norm]
    simp [u, norm_sub_rev]
  have hcommon_eqs :
      ∀ z : ℝ², dist q1 z = r → dist q2 z = s →
        ((X z + 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = ‖u‖ ^ 2 ∧
        ((X z - 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = s ^ 2 := by
    intro z hz1 hz2
    constructor
    · rw [← hdist_q1_sq z, hz1, ← hnorm_u]
    · rw [← hdist_q2_sq z, hz2]
  obtain ⟨ha_eq1, ha_eq2⟩ := hcommon_eqs a hr_q1a hs_q2a
  obtain ⟨hq_eq1, hq_eq2⟩ := hcommon_eqs q hr_q1q hs_q2q
  have hXdiff : (X q - X a) * (2 * ‖u‖ ^ 2) = 0 := by
    linear_combination hq_eq1 - hq_eq2 - ha_eq1 + ha_eq2
  have hqX_eq : X q = X a := by
    rcases mul_eq_zero.mp hXdiff with h | h
    · exact sub_eq_zero.mp h
    · nlinarith only [hu_sq_pos, h]
  have hYdiff : (Y q ^ 2 - Y a ^ 2) * ‖u‖ ^ 2 = 0 := by
    linear_combination hq_eq1 - ha_eq1 - (X q + X a + 1) * ‖u‖ ^ 2 * hqX_eq
  have hqY_sq : Y q ^ 2 = Y a ^ 2 := by
    rcases mul_eq_zero.mp hYdiff with h | h
    · exact sub_eq_zero.mp h
    · nlinarith only [hu_sq_pos, h]
  have hy_cases : Y q = Y a ∨ Y q = -Y a :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hqY_sq
  have h2XaU : 2 * X a * ‖u‖ ^ 2 = ‖u‖ ^ 2 - s ^ 2 := by
    linear_combination ha_eq1 - ha_eq2
  rcases hy_cases with hsame | hopp
  ·
    have hqa2 : q = a := by
      have hsub : q - M = a - M := by
        calc
          q - M = X q • u + Y q • nvec := hsum_pt q
          _ = X a • u + Y a • nvec := by rw [hqX_eq, hsame]
          _ = a - M := (hsum_pt a).symm
      have hadd := congrArg (fun t : ℝ² => t + M) hsub
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
    have ha_not_verts : a ∉ S.triangle.verts := by
      have ha_ne_v1 : a ≠ q1 := by
        unfold Problem97.FiniteEndpointShell.I2 at hA2
        exact (Finset.mem_erase.mp hA2).1
      have ha_ne_v3 : a ≠ S.triangle.v3 := by
        unfold Problem97.FiniteEndpointShell.I2 at hA2
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).1
      have ha_ne_v2 : a ≠ q2 := by
        intro h
        have : q2 ∈ S.CP.C2 := by simpa [h] using haC2
        exact S.CP.v2_notin_C2 this
      simp [Problem97.MoserTriangle.verts, q1, q2, ha_ne_v1, ha_ne_v2, ha_ne_v3]
    have hone_a := S.CP.nonmoser_in_one a haA ha_not_verts
    have haI1 : a ∈ S.I1 := by simpa [hqa2] using hqI1
    have haC1 : a ∈ S.CP.C1 := by
      unfold Problem97.FiniteEndpointShell.I1 at haI1
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase haI1)
    have hone_a' : (2 + if a ∈ S.CP.C3 then 1 else 0) = 1 := by
      simpa [haC1, haC2] using hone_a
    by_cases haC3 : a ∈ S.CP.C3 <;> simp [haC3] at hone_a'
  ·
    have hdisk_a : dist center a ≤ S.Packet.radius := by
      have hdisk_a' : ‖a - center‖ ≤ S.Packet.radius := by
        simpa [center] using S.Packet.disk_contains_A a haA
      rw [dist_eq_norm, norm_sub_rev]
      exact hdisk_a'
    have hradius : dist center q1 = S.Packet.radius := by
      rw [dist_comm, dist_eq_norm]
      exact S.Packet.moser_on_boundary_1
    have hdist_sq : dist center a ^ 2 ≤ dist center q1 ^ 2 := by
      have hnonneg_a : 0 ≤ dist center a := dist_nonneg
      have hnonneg_q1 : 0 ≤ dist center q1 := dist_nonneg
      nlinarith only [hdisk_a, hradius, hnonneg_a, hnonneg_q1]
    rw [hdist_center_sq a, hdist_center_sq q1, hX_q1, hY_q1] at hdist_sq
    have hyc_pos : 0 < Y a * yc := by
      nlinarith only [hs_sq_pos, ha_eq1, ha_eq2, hdist_sq, h2XaU, hu_sq_pos]
    have hq_out : dist center q > S.Packet.radius := by
      have hdist_sq_q : dist center q ^ 2 > S.Packet.radius ^ 2 := by
        rw [hdist_center_sq q]
        have hradius_sq :
            S.Packet.radius ^ 2 = ((1 / 2 : ℝ) ^ 2 + yc ^ 2) * ‖u‖ ^ 2 := by
          have hq1sq := hdist_center_sq q1
          rw [hradius, hX_q1, hY_q1] at hq1sq
          nlinarith only [hq1sq]
        rw [hqX_eq, hopp, hradius_sq]
        nlinarith only [hs_sq_pos, ha_eq1, ha_eq2, hdist_sq, h2XaU, hyc_pos, hu_sq_pos]
      have hrad_nn : 0 ≤ S.Packet.radius := le_of_lt S.Packet.radius_pos
      have hdist_nn : 0 ≤ dist center q := dist_nonneg
      nlinarith only [hdist_sq_q, hrad_nn, hdist_nn]
    have hdisk_q : dist center q ≤ S.Packet.radius := by
      have hdisk_q' : ‖q - center‖ ≤ S.Packet.radius := by
        simpa [center] using S.Packet.disk_contains_A q hqA
      rw [dist_eq_norm, norm_sub_rev]
      exact hdisk_q'
    exact absurd hdisk_q (not_le_of_gt hq_out)
theorem selectorShape_v2_lower_forces_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hB : S.IsFormB_v1 r)
    (hA2 : (Z.a2 : ℝ²) ∈ S.I2)
    (h_a2eq : S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²))
    (hI2sub : S.I2 ⊆ S.witnessClassAt_v2 s)
    {p : ℝ²}
    (hp : p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²))
    (hpeq : S.witnessClassAt_v2 s ∩ S.CP.C1 = ({p} : Finset ℝ²)) :
    S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) := by
  classical
  have hforce : S.SharedCirclePointForcesV3 Z r s :=
    S.sharedCirclePointForcesV3_of_formB_lower Z hs hB hA2 h_a2eq hI2sub
  have hcore := (p2mCoreSupport S).coreSelector_v1 hr hcard
  rcases hcore with ⟨-, hI1sub, -, -⟩
  have hpT2 : p ∈ S.witnessClassAt_v2 s := by
    have hpmem : p ∈ ({p} : Finset ℝ²) := by simp
    rw [← hpeq] at hpmem
    exact (Finset.mem_inter.mp hpmem).1
  rcases Finset.mem_insert.mp hp with hpa1 | hprest
  · have hpa1' : p = Z.a1 := by simpa using hpa1
    have ha1I1 : Z.a1 ∈ S.I1 := by
      rw [Z.hI1]
      simp
    have ha1T1 : Z.a1 ∈ S.witnessClassAt_v1 r := hI1sub ha1I1
    have hpv3 : p = S.triangle.v3 :=
      hforce p hp hpT2 (by simpa [hpa1'] using ha1T1)
    rwa [hpv3] at hpeq
  rcases Finset.mem_insert.mp hprest with hpb1 | hpv3
  · have hpb1' : p = Z.b1 := by simpa using hpb1
    have hb1I1 : Z.b1 ∈ S.I1 := by
      rw [Z.hI1]
      simp
    have hb1T1 : Z.b1 ∈ S.witnessClassAt_v1 r := hI1sub hb1I1
    have hpv3 : p = S.triangle.v3 :=
      hforce p hp hpT2 (by simpa [hpb1'] using hb1T1)
    rwa [hpv3] at hpeq
  · have hpv3' : p = S.triangle.v3 := by simpa using hpv3
    rwa [hpv3'] at hpeq
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit055

-- Original module: Solutions.Batch3N9.N4d.FormBPEqBProducer
section Batch3N9Unit056
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
abbrev SelectorV3PeqBPacket
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  FiniteEndpointShell.SelectorV3Pv2Packet S Z r
theorem b3n9m056_v1_lt_v1v3_of_mem_I2
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
        _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simp [hi_first]
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
      have hi_lt_top : i.val < m := i.is_lt
      have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
        intro hi_last
        apply hp_ne_v3
        calc
          p = L.points i := hi.symm
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
          _ = S.triangle.v3 := hLastFirst.2
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
theorem b3n9m056_v2_lt_v2v1_of_mem_I3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {q : ℝ²}
    (hqI3 : q ∈ S.I3) :
    dist S.triangle.v2 q < dist S.triangle.v2 S.triangle.v1 := by
  classical
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
        _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
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
          _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simp [hi_first]
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
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
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
theorem pEqB_column_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hlower : FormBv1A2SelectorV2LowerPacket S Z r s)
    (hpacket3 : SelectorV3PeqBPacket S Z t) :
    False := by
  classical
  rcases hlower with ⟨hA2, ha2eq, hTcard, hI2sub, hC1eq, hC3eq⟩
  rcases hpacket3 with ⟨hI3sub, hpBeq, hqeqC2⟩
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
  have hv2T3 : S.triangle.v2 ∈ S.witnessClassAt_v3 t := by
    have hmem : S.triangle.v2 ∈ ({S.triangle.v2} : Finset ℝ²) := by simp
    rw [← hpBeq] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hqT3 : q ∈ S.witnessClassAt_v3 t := hI3sub hqI3
  have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
    simpa using (Finset.mem_filter.mp hv3T).2
  have hqrad2 : dist S.triangle.v2 q = s := by
    simpa using (Finset.mem_filter.mp hqT2).2
  have hv2rad3 : dist S.triangle.v3 S.triangle.v2 = t := by
    simpa using (Finset.mem_filter.mp hv2T3).2
  have hqrad3 : dist S.triangle.v3 q = t := by
    simpa using (Finset.mem_filter.mp hqT3).2
  have hBq : dist S.triangle.v2 q = dist S.triangle.v2 S.triangle.v3 := by
    rw [hqrad2, hv3rad]
  have hDq : dist S.triangle.v3 q = dist S.triangle.v2 S.triangle.v3 := by
    rw [hqrad3, ← hv2rad3, dist_comm]
  have hsmall : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v1 S.triangle.v2 := by
    have hq_lt_base : dist S.triangle.v2 q < dist S.triangle.v2 S.triangle.v1 :=
      S.b3n9m056_v2_lt_v2v1_of_mem_I3 hqI3
    calc
      dist S.triangle.v2 S.triangle.v3 = dist S.triangle.v2 q := by rw [hBq]
      _ < dist S.triangle.v2 S.triangle.v1 := hq_lt_base
      _ = dist S.triangle.v1 S.triangle.v2 := by rw [dist_comm]
  have hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3 := by
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
    have h := S.b3n9m056_v1_lt_v1v3_of_mem_I2 (p := Z.a2) hA2
    rwa [← hbase_eq] at h
  exact S.pEqB_row_impossible_of_equilateral hqI3 hBq hDq hsmall hlong
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit056

-- Original module: Solutions.Batch3N9.N4d.Qa2Cover
section Batch3N9Unit061
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
theorem b3n9m061_classify_I1 {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {p : ℝ²} (hp : p ∈ S.I1) :
    p ∈ A ∧ p ∈ S.CP.C1 ∧ p ∉ S.CP.C2 ∧ p ∉ S.CP.C3 := by
  have hC1 : p ∈ S.CP.C1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).2
  have hne3 : p ≠ S.triangle.v3 := (Finset.mem_erase.mp hp).1
  have hne2 : p ≠ S.triangle.v2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
  have hne1 : p ≠ S.triangle.v1 := fun h => S.CP.v1_notin_C1 (h ▸ hC1)
  have hA : p ∈ A := S.CP.C1_subset hC1
  have hnm : p ∉ S.triangle.verts := by
    simp only [Problem97.MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
    push_neg; exact ⟨hne1, hne2, hne3⟩
  have hone := S.CP.nonmoser_in_one p hA hnm
  refine ⟨hA, hC1, ?_, ?_⟩
  · intro hC2; simp only [hC1, hC2, if_true] at hone
    by_cases hC3 : p ∈ S.CP.C3 <;> simp [hC3] at hone
  · intro hC3; simp only [hC1, hC3, if_true] at hone
    by_cases hC2 : p ∈ S.CP.C2 <;> simp [hC2] at hone
theorem b3n9m061_classify_I2 {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {p : ℝ²} (hp : p ∈ S.I2) :
    p ∈ A ∧ p ∉ S.CP.C1 ∧ p ∈ S.CP.C2 ∧ p ∉ S.CP.C3 := by
  have hC2 : p ∈ S.CP.C2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).2
  have hne1 : p ≠ S.triangle.v1 := (Finset.mem_erase.mp hp).1
  have hne3 : p ≠ S.triangle.v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
  have hne2 : p ≠ S.triangle.v2 := fun h => S.CP.v2_notin_C2 (h ▸ hC2)
  have hA : p ∈ A := S.CP.C2_subset hC2
  have hnm : p ∉ S.triangle.verts := by
    simp only [Problem97.MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
    push_neg; exact ⟨hne1, hne2, hne3⟩
  have hone := S.CP.nonmoser_in_one p hA hnm
  refine ⟨hA, ?_, hC2, ?_⟩
  · intro hC1; simp only [hC1, hC2, if_true] at hone
    by_cases hC3 : p ∈ S.CP.C3 <;> simp [hC3] at hone
  · intro hC3; simp only [hC2, hC3, if_true] at hone
    by_cases hC1 : p ∈ S.CP.C1 <;> simp [hC1] at hone
theorem b3n9m061_classify_I3 {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {p : ℝ²} (hp : p ∈ S.I3) :
    p ∈ A ∧ p ∉ S.CP.C1 ∧ p ∉ S.CP.C2 ∧ p ∈ S.CP.C3 := by
  have hC3 : p ∈ S.CP.C3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).2
  have hne2 : p ≠ S.triangle.v2 := (Finset.mem_erase.mp hp).1
  have hne1 : p ≠ S.triangle.v1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
  have hne3 : p ≠ S.triangle.v3 := fun h => S.CP.v3_notin_C3 (h ▸ hC3)
  have hA : p ∈ A := S.CP.C3_subset hC3
  have hnm : p ∉ S.triangle.verts := by
    simp only [Problem97.MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
    push_neg; exact ⟨hne1, hne2, hne3⟩
  have hone := S.CP.nonmoser_in_one p hA hnm
  refine ⟨hA, ?_, ?_, hC3⟩
  · intro hC1; simp only [hC1, hC3, if_true] at hone
    by_cases hC2 : p ∈ S.CP.C2 <;> simp [hC2] at hone
  · intro hC2; simp only [hC2, hC3, if_true] at hone
    by_cases hC1 : p ∈ S.CP.C1 <;> simp [hC1] at hone
theorem b3n9m061_ne_of_mem_not_mem {α : Type*} {C : Finset α} {p q : α}
    (hp : p ∈ C) (hq : q ∉ C) : p ≠ q := fun h => hq (h ▸ hp)
theorem A_eq_named {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) :
    A = ({S.triangle.v1, S.triangle.v2, S.triangle.v3, Z.a1, Z.b1, Z.a2, Z.b2, Z.a3, Z.b3}
      : Finset ℝ²) := by
  classical
  have ha1 := S.b3n9m061_classify_I1 (show Z.a1 ∈ S.I1 by rw [Z.hI1]; simp)
  have hb1 := S.b3n9m061_classify_I1 (show Z.b1 ∈ S.I1 by rw [Z.hI1]; simp)
  have ha2 := S.b3n9m061_classify_I2 (show Z.a2 ∈ S.I2 by rw [Z.hI2]; simp)
  have hb2 := S.b3n9m061_classify_I2 (show Z.b2 ∈ S.I2 by rw [Z.hI2]; simp)
  have ha3 := S.b3n9m061_classify_I3 (show Z.a3 ∈ S.I3 by rw [Z.hI3]; simp)
  have hb3 := S.b3n9m061_classify_I3 (show Z.b3 ∈ S.I3 by rw [Z.hI3]; simp)
  have v1c1 : S.triangle.v1 ∉ S.CP.C1 := S.CP.v1_notin_C1
  have v1c2 : S.triangle.v1 ∈ S.CP.C2 := S.CP.v1_mem_C2
  have v1c3 : S.triangle.v1 ∈ S.CP.C3 := S.CP.v1_mem_C3
  have v2c1 : S.triangle.v2 ∈ S.CP.C1 := S.CP.v2_mem_C1
  have v2c2 : S.triangle.v2 ∉ S.CP.C2 := S.CP.v2_notin_C2
  have v2c3 : S.triangle.v2 ∈ S.CP.C3 := S.CP.v2_mem_C3
  have v3c1 : S.triangle.v3 ∈ S.CP.C1 := S.CP.v3_mem_C1
  have v3c2 : S.triangle.v3 ∈ S.CP.C2 := S.CP.v3_mem_C2
  have v3c3 : S.triangle.v3 ∉ S.CP.C3 := S.CP.v3_notin_C3
  obtain ⟨_, a1c1, a1c2, a1c3⟩ := ha1
  obtain ⟨_, b1c1, b1c2, b1c3⟩ := hb1
  obtain ⟨_, a2c1, a2c2, a2c3⟩ := ha2
  obtain ⟨_, b2c1, b2c2, b2c3⟩ := hb2
  obtain ⟨_, a3c1, a3c2, a3c3⟩ := ha3
  obtain ⟨_, b3c1, b3c2, b3c3⟩ := hb3
  have e_a1b1 : Z.a1 ≠ Z.b1 := by
    have h : ({Z.a1, Z.b1} : Finset ℝ²).card = 2 := by simpa [Z.hI1] using (p2mCoreSupport S).I1_card_eq_two
    intro h'; simp [h'] at h
  have e_a2b2 : Z.a2 ≠ Z.b2 := by
    have h : ({Z.a2, Z.b2} : Finset ℝ²).card = 2 := by simpa [Z.hI2] using (p2mCoreSupport S).I2_card_eq_two
    intro h'; simp [h'] at h
  have e_a3b3 : Z.a3 ≠ Z.b3 := by
    have h : ({Z.a3, Z.b3} : Finset ℝ²).card = 2 := by simpa [Z.hI3] using (p2mCoreSupport S).I3_card_eq_two
    intro h'; simp [h'] at h
  have e_v1v2 : S.triangle.v1 ≠ S.triangle.v2 := b3n9m061_ne_of_mem_not_mem v1c2 v2c2
  have e_v1v3 : S.triangle.v1 ≠ S.triangle.v3 := b3n9m061_ne_of_mem_not_mem v1c3 v3c3
  have e_v1a1 : S.triangle.v1 ≠ Z.a1 := b3n9m061_ne_of_mem_not_mem v1c2 a1c2
  have e_v1b1 : S.triangle.v1 ≠ Z.b1 := b3n9m061_ne_of_mem_not_mem v1c2 b1c2
  have e_v1a2 : S.triangle.v1 ≠ Z.a2 := b3n9m061_ne_of_mem_not_mem v1c3 a2c3
  have e_v1b2 : S.triangle.v1 ≠ Z.b2 := b3n9m061_ne_of_mem_not_mem v1c3 b2c3
  have e_v1a3 : S.triangle.v1 ≠ Z.a3 := b3n9m061_ne_of_mem_not_mem v1c2 a3c2
  have e_v1b3 : S.triangle.v1 ≠ Z.b3 := b3n9m061_ne_of_mem_not_mem v1c2 b3c2
  have e_v2v3 : S.triangle.v2 ≠ S.triangle.v3 := b3n9m061_ne_of_mem_not_mem v2c3 v3c3
  have e_v2a1 : S.triangle.v2 ≠ Z.a1 := b3n9m061_ne_of_mem_not_mem v2c3 a1c3
  have e_v2b1 : S.triangle.v2 ≠ Z.b1 := b3n9m061_ne_of_mem_not_mem v2c3 b1c3
  have e_v2a2 : S.triangle.v2 ≠ Z.a2 := b3n9m061_ne_of_mem_not_mem v2c1 a2c1
  have e_v2b2 : S.triangle.v2 ≠ Z.b2 := b3n9m061_ne_of_mem_not_mem v2c1 b2c1
  have e_v2a3 : S.triangle.v2 ≠ Z.a3 := b3n9m061_ne_of_mem_not_mem v2c1 a3c1
  have e_v2b3 : S.triangle.v2 ≠ Z.b3 := b3n9m061_ne_of_mem_not_mem v2c1 b3c1
  have e_v3a1 : S.triangle.v3 ≠ Z.a1 := b3n9m061_ne_of_mem_not_mem v3c2 a1c2
  have e_v3b1 : S.triangle.v3 ≠ Z.b1 := b3n9m061_ne_of_mem_not_mem v3c2 b1c2
  have e_v3a2 : S.triangle.v3 ≠ Z.a2 := b3n9m061_ne_of_mem_not_mem v3c1 a2c1
  have e_v3b2 : S.triangle.v3 ≠ Z.b2 := b3n9m061_ne_of_mem_not_mem v3c1 b2c1
  have e_v3a3 : S.triangle.v3 ≠ Z.a3 := b3n9m061_ne_of_mem_not_mem v3c1 a3c1
  have e_v3b3 : S.triangle.v3 ≠ Z.b3 := b3n9m061_ne_of_mem_not_mem v3c1 b3c1
  have e_a1a2 : Z.a1 ≠ Z.a2 := b3n9m061_ne_of_mem_not_mem a1c1 a2c1
  have e_a1b2 : Z.a1 ≠ Z.b2 := b3n9m061_ne_of_mem_not_mem a1c1 b2c1
  have e_a1a3 : Z.a1 ≠ Z.a3 := b3n9m061_ne_of_mem_not_mem a1c1 a3c1
  have e_a1b3 : Z.a1 ≠ Z.b3 := b3n9m061_ne_of_mem_not_mem a1c1 b3c1
  have e_b1a2 : Z.b1 ≠ Z.a2 := b3n9m061_ne_of_mem_not_mem b1c1 a2c1
  have e_b1b2 : Z.b1 ≠ Z.b2 := b3n9m061_ne_of_mem_not_mem b1c1 b2c1
  have e_b1a3 : Z.b1 ≠ Z.a3 := b3n9m061_ne_of_mem_not_mem b1c1 a3c1
  have e_b1b3 : Z.b1 ≠ Z.b3 := b3n9m061_ne_of_mem_not_mem b1c1 b3c1
  have e_a2a3 : Z.a2 ≠ Z.a3 := b3n9m061_ne_of_mem_not_mem a2c2 a3c2
  have e_a2b3 : Z.a2 ≠ Z.b3 := b3n9m061_ne_of_mem_not_mem a2c2 b3c2
  have e_b2a3 : Z.b2 ≠ Z.a3 := b3n9m061_ne_of_mem_not_mem b2c2 a3c2
  have e_b2b3 : Z.b2 ≠ Z.b3 := b3n9m061_ne_of_mem_not_mem b2c2 b3c2
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact S.triangle.v1_mem
    · exact S.triangle.v2_mem
    · exact S.triangle.v3_mem
    · exact S.CP.C1_subset a1c1
    · exact S.CP.C1_subset b1c1
    · exact S.CP.C2_subset a2c2
    · exact S.CP.C2_subset b2c2
    · exact S.CP.C3_subset a3c3
    · exact S.CP.C3_subset b3c3
  · rw [S.hcard9]
    have hcard :
        ({S.triangle.v1, S.triangle.v2, S.triangle.v3, Z.a1, Z.b1, Z.a2, Z.b2, Z.a3, Z.b3}
          : Finset ℝ²).card = 9 := by
      rw [Finset.card_insert_of_notMem (by
            simp [e_v1v2, e_v1v3, e_v1a1, e_v1b1, e_v1a2, e_v1b2, e_v1a3, e_v1b3]),
          Finset.card_insert_of_notMem (by
            simp [e_v2v3, e_v2a1, e_v2b1, e_v2a2, e_v2b2, e_v2a3, e_v2b3]),
          Finset.card_insert_of_notMem (by
            simp [e_v3a1, e_v3b1, e_v3a2, e_v3b2, e_v3a3, e_v3b3]),
          Finset.card_insert_of_notMem (by simp [e_a1b1, e_a1a2, e_a1b2, e_a1a3, e_a1b3]),
          Finset.card_insert_of_notMem (by simp [e_b1a2, e_b1b2, e_b1a3, e_b1b3]),
          Finset.card_insert_of_notMem (by simp [e_a2b2, e_a2a3, e_a2b3]),
          Finset.card_insert_of_notMem (by simp [e_b2a3, e_b2b3]),
          Finset.card_insert_of_notMem (by simp [e_a3b3]),
          Finset.card_singleton]
    rw [hcard]
theorem b3n9m061_hXeq_transport_v2 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V2AnchorFrame S Z) {P Q x : ℝ²} {r : ℝ}
    (hP : dist x P = r) (hQ : dist x Q = r) :
    dist (F.T x) (F.T P) = dist (F.T x) (F.T Q) := by
  rw [F.tau.dist_image, F.tau.dist_image, hP, hQ]
theorem b3n9m061_hXeq_transport_v1 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V1AnchorFrame S Z) {P Q x : ℝ²} {r : ℝ}
    (hP : dist x P = r) (hQ : dist x Q = r) :
    dist (F.base.T x) (F.base.T P) = dist (F.base.T x) (F.base.T Q) := by
  rw [F.base.tau.dist_image, F.base.tau.dist_image, hP, hQ]
theorem b3n9m061_kill_v1a2 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V2AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.T Z.a3) 1 ≤ 0) (ha3v2 : Z.a3 ≠ S.triangle.v2)
    (hP : dist Z.a3 S.triangle.v1 = r) (hQ : dist Z.a3 Z.a2 = r) : False := by
  obtain ⟨hXdisk, hBeq, hBy0, hXy, hdy, hinner, hPQ, hXne⟩ :=
    F.bisectorKill_args_v1a2 ha3A ha3y ha3v2
  exact Problem97.bisectorKill (F.T S.triangle.v2) (F.T S.Packet.center)
    (F.T S.triangle.v1) (F.T Z.a2) (F.T Z.a3)
    hXdisk (b3n9m061_hXeq_transport_v2 F hP hQ) hBeq hBy0 hXy hdy hinner hPQ hXne
theorem b3n9m061_kill_v3a2 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V2AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.T Z.a3) 1 ≤ 0) (ha3v2 : Z.a3 ≠ S.triangle.v2)
    (hP : dist Z.a3 S.triangle.v3 = r) (hQ : dist Z.a3 Z.a2 = r) : False := by
  obtain ⟨hXdisk, hBeq, hBy0, hXy, hdy, hinner, hPQ, hXne⟩ :=
    F.bisectorKill_args_v3a2 ha3A ha3y ha3v2
  exact Problem97.bisectorKill (F.T S.triangle.v2) (F.T S.Packet.center)
    (F.T S.triangle.v3) (F.T Z.a2) (F.T Z.a3)
    hXdisk (b3n9m061_hXeq_transport_v2 F hP hQ) hBeq hBy0 hXy hdy hinner hPQ hXne
theorem b3n9m061_kill_v1b2 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V2AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.T Z.a3) 1 ≤ 0) (ha3v2 : Z.a3 ≠ S.triangle.v2)
    (hP : dist Z.a3 S.triangle.v1 = r) (hQ : dist Z.a3 Z.b2 = r) : False := by
  obtain ⟨hXdisk, hBeq, hBy0, hXy, hdy, hinner, hPQ, hXne⟩ :=
    F.bisectorKill_args_v1b2 ha3A ha3y ha3v2
  exact Problem97.bisectorKill (F.T S.triangle.v2) (F.T S.Packet.center)
    (F.T S.triangle.v1) (F.T Z.b2) (F.T Z.a3)
    hXdisk (b3n9m061_hXeq_transport_v2 F hP hQ) hBeq hBy0 hXy hdy hinner hPQ hXne
theorem b3n9m061_kill_v3b2 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V2AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.T Z.a3) 1 ≤ 0) (ha3v2 : Z.a3 ≠ S.triangle.v2)
    (hP : dist Z.a3 S.triangle.v3 = r) (hQ : dist Z.a3 Z.b2 = r) : False := by
  obtain ⟨hXdisk, hBeq, hBy0, hXy, hdy, hinner, hPQ, hXne⟩ :=
    F.bisectorKill_args_v3b2 ha3A ha3y ha3v2
  exact Problem97.bisectorKill (F.T S.triangle.v2) (F.T S.Packet.center)
    (F.T S.triangle.v3) (F.T Z.b2) (F.T Z.a3)
    hXdisk (b3n9m061_hXeq_transport_v2 F hP hQ) hBeq hBy0 hXy hdy hinner hPQ hXne
theorem b3n9m061_kill_a2b2 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V2AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.T Z.a3) 1 ≤ 0) (ha3v2 : Z.a3 ≠ S.triangle.v2)
    (hP : dist Z.a3 Z.a2 = r) (hQ : dist Z.a3 Z.b2 = r) : False := by
  obtain ⟨hXdisk, hBeq, hBy0, hXy, hdy, hinner, hPQ, hXne⟩ :=
    F.bisectorKill_args_a2b2 ha3A ha3y ha3v2
  exact Problem97.bisectorKill (F.T S.triangle.v2) (F.T S.Packet.center)
    (F.T Z.a2) (F.T Z.b2) (F.T Z.a3)
    hXdisk (b3n9m061_hXeq_transport_v2 F hP hQ) hBeq hBy0 hXy hdy hinner hPQ hXne
theorem b3n9m061_kill_v1v3 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V2AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.T Z.a3) 1 ≤ 0) (ha3v2 : Z.a3 ≠ S.triangle.v2)
    (hP : dist Z.a3 S.triangle.v1 = r) (hQ : dist Z.a3 S.triangle.v3 = r) : False := by
  obtain ⟨hXdisk, hBeq, hBy0, hXy, hdy, hinner, hPQ, hXne⟩ :=
    F.bisectorKill_args_v1v3 ha3A ha3y ha3v2
  exact Problem97.bisectorKill (F.T S.triangle.v2) (F.T S.Packet.center)
    (F.T S.triangle.v1) (F.T S.triangle.v3) (F.T Z.a3)
    hXdisk (b3n9m061_hXeq_transport_v2 F hP hQ) hBeq hBy0 hXy hdy hinner hPQ hXne
theorem b3n9m061_kill_a1b1 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V1AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.base.T Z.a3) 1 ≤ 0) (ha3v1 : Z.a3 ≠ S.triangle.v1)
    (hP : dist Z.a3 Z.a1 = r) (hQ : dist Z.a3 Z.b1 = r) : False := by
  obtain ⟨hXdisk, hBeq, hBy0, hXy, hdy, hinner, hPQ, hXne⟩ :=
    F.bisectorKill_args_a1b1 ha3A ha3y ha3v1
  exact Problem97.bisectorKill (F.base.T S.triangle.v1) (F.base.T S.Packet.center)
    (F.base.T Z.a1) (F.base.T Z.b1) (F.base.T Z.a3)
    hXdisk (b3n9m061_hXeq_transport_v1 F hP hQ) hBeq hBy0 hXy hdy hinner hPQ hXne
theorem b3n9m061_kill_v2a1 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V1AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.base.T Z.a3) 1 ≤ 0) (ha3v1 : Z.a3 ≠ S.triangle.v1)
    (hP : dist Z.a3 S.triangle.v2 = r) (hQ : dist Z.a3 Z.a1 = r) : False := by
  obtain ⟨hXdisk, hBeq, hBy0, hXy, hdy, hinner, hPQ, hXne⟩ :=
    F.bisectorKill_args_v2a1 ha3A ha3y ha3v1
  exact Problem97.bisectorKill (F.base.T S.triangle.v1) (F.base.T S.Packet.center)
    (F.base.T S.triangle.v2) (F.base.T Z.a1) (F.base.T Z.a3)
    hXdisk (b3n9m061_hXeq_transport_v1 F hP hQ) hBeq hBy0 hXy hdy hinner hPQ hXne
theorem b3n9m061_kill_v2b1 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V1AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.base.T Z.a3) 1 ≤ 0) (ha3v1 : Z.a3 ≠ S.triangle.v1)
    (hP : dist Z.a3 S.triangle.v2 = r) (hQ : dist Z.a3 Z.b1 = r) : False := by
  obtain ⟨hXdisk, hBeq, hBy0, hXy, hdy, hinner, hPQ, hXne⟩ :=
    F.bisectorKill_args_v2b1 ha3A ha3y ha3v1
  exact Problem97.bisectorKill (F.base.T S.triangle.v1) (F.base.T S.Packet.center)
    (F.base.T S.triangle.v2) (F.base.T Z.b1) (F.base.T Z.a3)
    hXdisk (b3n9m061_hXeq_transport_v1 F hP hQ) hBeq hBy0 hXy hdy hinner hPQ hXne
theorem b3n9m061_kill_KA {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V2AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.T Z.a3) 1 ≤ 0) (ha3v2 : Z.a3 ≠ S.triangle.v2)
    {p q : ℝ²}
    (hp : p ∈ ({S.triangle.v1, S.triangle.v3, Z.a2, Z.b2} : Finset ℝ²))
    (hq : q ∈ ({S.triangle.v1, S.triangle.v3, Z.a2, Z.b2} : Finset ℝ²))
    (hpq : p ≠ q) (hpr : dist Z.a3 p = r) (hqr : dist Z.a3 q = r) : False := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
  · exact hpq rfl
  · exact b3n9m061_kill_v1v3 F ha3A ha3y ha3v2 hpr hqr
  · exact b3n9m061_kill_v1a2 F ha3A ha3y ha3v2 hpr hqr
  · exact b3n9m061_kill_v1b2 F ha3A ha3y ha3v2 hpr hqr
  · exact b3n9m061_kill_v1v3 F ha3A ha3y ha3v2 hqr hpr
  · exact hpq rfl
  · exact b3n9m061_kill_v3a2 F ha3A ha3y ha3v2 hpr hqr
  · exact b3n9m061_kill_v3b2 F ha3A ha3y ha3v2 hpr hqr
  · exact b3n9m061_kill_v1a2 F ha3A ha3y ha3v2 hqr hpr
  · exact b3n9m061_kill_v3a2 F ha3A ha3y ha3v2 hqr hpr
  · exact hpq rfl
  · exact b3n9m061_kill_a2b2 F ha3A ha3y ha3v2 hpr hqr
  · exact b3n9m061_kill_v1b2 F ha3A ha3y ha3v2 hqr hpr
  · exact b3n9m061_kill_v3b2 F ha3A ha3y ha3v2 hqr hpr
  · exact b3n9m061_kill_a2b2 F ha3A ha3y ha3v2 hqr hpr
  · exact hpq rfl
theorem b3n9m061_kill_KB {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {Z : ZeroDefectCapLayout S} (F : V1AnchorFrame S Z) {r : ℝ}
    (ha3A : Z.a3 ∈ A) (ha3y : (F.base.T Z.a3) 1 ≤ 0) (ha3v1 : Z.a3 ≠ S.triangle.v1)
    {p q : ℝ²}
    (hp : p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²))
    (hq : q ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²))
    (hpq : p ≠ q) (hpr : dist Z.a3 p = r) (hqr : dist Z.a3 q = r) : False := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact hpq rfl
  · exact b3n9m061_kill_a1b1 F ha3A ha3y ha3v1 hpr hqr
  · exact b3n9m061_kill_v2a1 F ha3A ha3y ha3v1 hqr hpr
  · exact b3n9m061_kill_a1b1 F ha3A ha3y ha3v1 hqr hpr
  · exact hpq rfl
  · exact b3n9m061_kill_v2b1 F ha3A ha3y ha3v1 hqr hpr
  · exact b3n9m061_kill_v2a1 F ha3A ha3y ha3v1 hpr hqr
  · exact b3n9m061_kill_v2b1 F ha3A ha3y ha3v1 hpr hqr
  · exact hpq rfl
theorem a3_k4_cover {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hC3pin : S.witnessClassAt_v1 r ∩ S.CP.C3 = ({S.triangle.v2} : Finset ℝ²))
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    False := by
  classical
  let F2 := S.v2AnchorFrame_of_hexact Z hexact
  let F1 := S.v1AnchorFrame_of_hexact Z hC3pin hcard hexact
  have ha3I3 : Z.a3 ∈ S.I3 := by rw [Z.hI3]; simp
  obtain ⟨ha3A, _, _, _⟩ := S.b3n9m061_classify_I3 ha3I3
  have ha3ne : Z.a3 ≠ S.triangle.v1 ∧ Z.a3 ≠ S.triangle.v2 := by
    have hne1 : Z.a3 ≠ S.triangle.v1 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha3I3).2).1
    have hne2 : Z.a3 ≠ S.triangle.v2 := (Finset.mem_erase.mp ha3I3).1
    exact ⟨hne1, hne2⟩
  obtain ⟨r2, hr2pos, hTcard⟩ := S.hK4 Z.a3 ha3A
  set T : Finset ℝ² := A.filter (fun x => dist Z.a3 x = r2) with hTdef
  have hT4 : 4 ≤ T.card := hTcard
  have ha3notT : Z.a3 ∉ T := by
    rw [hTdef]; simp only [Finset.mem_filter]
    rintro ⟨_, hd⟩; rw [dist_self] at hd; exact absurd hd.symm (ne_of_gt hr2pos)
  have hTsub : T ⊆ ({S.triangle.v1, S.triangle.v2, S.triangle.v3, Z.a1, Z.b1, Z.a2, Z.b2, Z.b3}
      : Finset ℝ²) := by
    intro x hxT
    have hxA : x ∈ A := (Finset.mem_filter.mp hxT).1
    have hxne_a3 : x ≠ Z.a3 := fun h => ha3notT (h ▸ hxT)
    have hx9 : x ∈ ({S.triangle.v1, S.triangle.v2, S.triangle.v3, Z.a1, Z.b1, Z.a2, Z.b2,
        Z.a3, Z.b3} : Finset ℝ²) := by rw [← S.A_eq_named Z]; exact hxA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx9 ⊢
    rcases hx9 with h|h|h|h|h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact absurd h hxne_a3
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  set KA : Finset ℝ² := {S.triangle.v1, S.triangle.v3, Z.a2, Z.b2} with hKA
  set KB : Finset ℝ² := {Z.a1, Z.b1, S.triangle.v2} with hKB
  have hpigeon : 2 ≤ (T ∩ KA).card ∨ 2 ≤ (T ∩ KB).card := by
    by_contra h
    push_neg at h
    obtain ⟨hAlt, hBlt⟩ := h
    have hsub : T ⊆ KA ∪ KB ∪ {Z.b3} := by
      intro x hx
      have := hTsub hx
      simp only [hKA, hKB, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
    have h1 : T ⊆ (T ∩ KA) ∪ (T ∩ KB) ∪ (T ∩ {Z.b3}) := by
      intro x hx
      have := hsub hx
      simp only [Finset.mem_union, Finset.mem_inter] at this ⊢
      tauto
    have hb : (T ∩ {Z.b3}).card ≤ 1 := by
      calc (T ∩ {Z.b3}).card ≤ ({Z.b3} : Finset ℝ²).card :=
            Finset.card_le_card Finset.inter_subset_right
        _ = 1 := Finset.card_singleton _
    have hle3 : T.card ≤ 3 := by
      calc T.card ≤ ((T ∩ KA) ∪ (T ∩ KB) ∪ (T ∩ {Z.b3})).card := Finset.card_le_card h1
        _ ≤ (T ∩ KA).card + (T ∩ KB).card + (T ∩ {Z.b3}).card := by
            refine le_trans (Finset.card_union_le _ _) ?_
            exact Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ ≤ 3 := by omega
    omega
  have ha3yF2 : (F2.T Z.a3) 1 ≤ 0 := F2.ha3_y
  have ha3yF1 : (F1.base.T Z.a3) 1 ≤ 0 := F1.base.ha3_y
  rcases hpigeon with hKA2 | hKB2
  · obtain ⟨p, hpKA, q, hqKA, hpq⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (T ∩ KA).card)
    have hpT := Finset.mem_of_mem_inter_left hpKA
    have hqT := Finset.mem_of_mem_inter_left hqKA
    have hpKA' := Finset.mem_of_mem_inter_right hpKA
    have hqKA' := Finset.mem_of_mem_inter_right hqKA
    have hpr : dist Z.a3 p = r2 := (Finset.mem_filter.mp hpT).2
    have hqr : dist Z.a3 q = r2 := (Finset.mem_filter.mp hqT).2
    exact b3n9m061_kill_KA F2 ha3A ha3yF2 ha3ne.2 hpKA' hqKA' hpq hpr hqr
  · obtain ⟨p, hpKB, q, hqKB, hpq⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (T ∩ KB).card)
    have hpT := Finset.mem_of_mem_inter_left hpKB
    have hqT := Finset.mem_of_mem_inter_left hqKB
    have hpKB' := Finset.mem_of_mem_inter_right hpKB
    have hqKB' := Finset.mem_of_mem_inter_right hqKB
    have hpr : dist Z.a3 p = r2 := (Finset.mem_filter.mp hpT).2
    have hqr : dist Z.a3 q = r2 := (Finset.mem_filter.mp hqT).2
    exact b3n9m061_kill_KB F1 ha3A ha3yF1 ha3ne.1 hpKB' hqKB' hpq hpr hqr
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit061

-- Original module: Solutions.Batch3N9.N4d.FormBXb2UpperArc
section Batch3N9Unit062
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
def SelectorV3Qb2Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (t : ℝ) : Prop :=
  let T := S.witnessClassAt_v3 t
  S.I3 ⊆ T ∧
    ∃ p : ℝ²,
      p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
        T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
          T ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²)
def Xb2Pin
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  ∃ _ : (Z.b2 : ℝ²) ∈ S.I2,
    S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²)
def AInSBPin
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (s : ℝ) : Prop :=
  0 < s ∧ SelectorV2Qv1Packet S Z s
theorem b3n9m062_witnessClassAt_v1_radius_pos_of_card_ge_four
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card) :
    0 < r := by
  have hpos : 0 < (S.witnessClassAt_v1 r).card := by
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hr_nonneg : 0 ≤ r := by
    have hxdist : dist S.triangle.v1 x = r := (Finset.mem_filter.mp hx).2
    have : 0 ≤ dist S.triangle.v1 x := dist_nonneg
    linarith
  by_contra hnot
  have hr0 : r = 0 := by
    linarith
  have hsubset :
      S.witnessClassAt_v1 r ⊆ ({S.triangle.v1} : Finset ℝ²) := by
    intro y hy
    have hydist : dist S.triangle.v1 y = r := (Finset.mem_filter.mp hy).2
    have hy0 : dist S.triangle.v1 y = 0 := by
      simpa [hr0] using hydist
    have hy_eq : y = S.triangle.v1 := by
      have : S.triangle.v1 = y := dist_eq_zero.mp hy0
      simpa using this.symm
    simp [hy_eq]
  have hcard_le :
      (S.witnessClassAt_v1 r).card ≤ ({S.triangle.v1} : Finset ℝ²).card :=
    Finset.card_le_card hsubset
  have : (S.witnessClassAt_v1 r).card ≤ 1 := by
    simpa using hcard_le
  omega
theorem b3n9m062_formBv1B2Packet_of_pins
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r : ℝ}
    (hB : S.IsFormB_v1 r) (hxb2 : Xb2Pin S Z r) :
    FormBv1B2Packet S Z r := by
  rcases hB with ⟨_, _, _, hv2eq⟩
  rcases hxb2 with ⟨hb2I2, hb2eq⟩
  exact ⟨hb2I2, hb2eq, hv2eq⟩
theorem b3n9m062_formBv1B2SelectorV2Qv1Packet_of_pins
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hB : S.IsFormB_v1 r) (hxb2 : Xb2Pin S Z r)
    (hAinSB : AInSBPin S Z s) :
    FormBv1B2SelectorV2Qv1Packet S Z r s := by
  rcases hAinSB with ⟨hs, hselector⟩
  exact ⟨S.b3n9m062_formBv1B2Packet_of_pins Z hB hxb2, hs, hselector⟩
theorem b3n9m062_selectorShape_v2_q_eq_v1_exact_packet_of_pins
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hB : S.IsFormB_v1 r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hxb2 : Xb2Pin S Z r) (hAinSB : AInSBPin S Z s) :
    S.witnessClassAt_v2 s =
      insert Z.a2
        (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
  have hr := S.b3n9m062_witnessClassAt_v1_radius_pos_of_card_ge_four hcard
  have hbranch := S.b3n9m062_formBv1B2SelectorV2Qv1Packet_of_pins Z hB hxb2 hAinSB
  have hlocal :
      FormBv1B2SelectorV2Qv1Packet S Z r s →
        S.witnessClassAt_v2 s =
          insert Z.a2
            (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
    dsimp [FormBv1B2SelectorV2Qv1Packet, FormBv1B2Packet, SelectorV2Qv1Packet]
    exact S.selectorShape_v2_q_eq_v1_exact_packet_of_b2
      (Z := Z) (r := r) (s := s) hr hcard
  exact hlocal hbranch
theorem b3n9m062_selectorShape_v3_q_eq_v1_impossible_of_pins
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hxb2 : Xb2Pin S Z r) (hAinSB : AInSBPin S Z s)
    (hpacket : SelectorV3Qv1Packet S Z t) :
    False := by
  have hbranch := S.b3n9m062_formBv1B2SelectorV2Qv1Packet_of_pins Z hB hxb2 hAinSB
  have hexact := S.b3n9m062_selectorShape_v2_q_eq_v1_exact_packet_of_pins
    Z hB hcard hxb2 hAinSB
  have hlocal :
      FormBv1B2SelectorV2Qv1Packet S Z r s →
        S.witnessClassAt_v2 s =
          insert Z.a2
            (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) →
          SelectorV3Qv1Packet S Z t →
            False := by
    dsimp [FormBv1B2SelectorV2Qv1Packet, FormBv1B2Packet]
    dsimp [SelectorV2Qv1Packet, SelectorV3Qv1Packet]
    exact S.selectorShape_v3_q_eq_v1_impossible_of_b2_exact_packet
      (Z := Z) (r := r) (s := s) (t := t)
  exact hlocal hbranch hexact hpacket
theorem b3n9m062_selectorShape_v3_q_eq_a2_nonwitness_upperArc_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hbranch : FormBv1B2SelectorV2Qv1Packet S Z r s)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2
        (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)))
    (hpacket : SelectorV3Qa2Packet S Z t) :
    False := by
  let _ := hpacket
  exact S.a3_k4_cover Z hbranch.1.2.2 hcard hexact
theorem b3n9m062_selectorShape_v3_q_eq_a2_impossible_of_pins
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hxb2 : Xb2Pin S Z r) (hAinSB : AInSBPin S Z s)
    (hpacket : SelectorV3Qa2Packet S Z t) :
    False := by
  have hbranch := S.b3n9m062_formBv1B2SelectorV2Qv1Packet_of_pins Z hB hxb2 hAinSB
  have hexact := S.b3n9m062_selectorShape_v2_q_eq_v1_exact_packet_of_pins
    Z hB hcard hxb2 hAinSB
  exact S.b3n9m062_selectorShape_v3_q_eq_a2_nonwitness_upperArc_impossible
    Z hbranch hcard hexact hpacket
theorem b3n9m062_selectorShape_v3_q_eq_b2_impossible_of_pins
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hxb2 : Xb2Pin S Z r) (hAinSB : AInSBPin S Z s)
    (hpacket : SelectorV3Qb2Packet S Z t) :
    False := by
  have hbranch0 := S.b3n9m062_formBv1B2SelectorV2Qv1Packet_of_pins Z hB hxb2 hAinSB
  rcases hbranch0 with ⟨⟨hb2I2, hb2eq, hv2eq⟩, hs, hselector⟩
  have hbranch' : FormBv1A2SelectorV2Qv1Packet S Z.swapI2 r s := by
    refine ⟨?_, hs, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [ZeroDefectCapLayout.swapI2] using hb2I2
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hb2eq
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hv2eq
    · simpa [SelectorV2Qv1Packet, ZeroDefectCapLayout.swapI2] using hselector
  have hexact := S.b3n9m062_selectorShape_v2_q_eq_v1_exact_packet_of_pins
    Z hB hcard hxb2 hAinSB
  have hswap :
      S.witnessClassAt_v2 s =
        insert Z.swapI2.a2
          (insert Z.swapI2.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
    ext x
    simp [ZeroDefectCapLayout.swapI2, hexact, Finset.mem_insert]
    simp [or_left_comm]
  have hpacket' : SelectorV3Qa2Packet S Z.swapI2 t := by
    simpa [SelectorV3Qa2Packet, SelectorV3Qb2Packet, ZeroDefectCapLayout.swapI2]
      using hpacket
  have hlocal :
      FormBv1A2SelectorV2Qv1Packet S Z.swapI2 r s →
        S.witnessClassAt_v2 s =
          insert Z.swapI2.a2
            (insert Z.swapI2.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) →
          SelectorV3Qa2Packet S Z.swapI2 t →
            False := by
    dsimp [FormBv1A2SelectorV2Qv1Packet, FormBv1A2Packet]
    dsimp [SelectorV2Qv1Packet, SelectorV3Qa2Packet]
    exact (p2mBranchSupport S Z.swapI2).selectorShape_v3_q_eq_a2_impossible_of_exact_packet
      (r := r) (s := s) (t := t)
  exact hlocal hbranch' hswap hpacket'
theorem b3n9m062_selectorShape_v3_split_local
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) :
    ∃ t : ℝ, 0 < t ∧ SelectorV3SplitPacket S Z t := by
  rcases (p2mCoreSupport S).selectorShape_v3_split Z with ⟨t, ht, hsplit⟩
  exact ⟨t, ht, by simpa [SelectorV3SplitPacket] using hsplit⟩
theorem n4d_bB1_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hB : S.IsFormB_v1 r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hxb2 : Xb2Pin S Z r)
    (hAinSB : AInSBPin S Z s) :
    False := by
  rcases S.b3n9m062_selectorShape_v3_split_local Z with ⟨t, _, hsplit⟩
  rcases hsplit with ⟨_, hI3sub, hcases⟩
  rcases hcases with hqv1 | hrest
  · have hpacket : SelectorV3Qv1Packet S Z t := by
      dsimp [SelectorV3Qv1Packet]
      exact hqv1
    exact S.b3n9m062_selectorShape_v3_q_eq_v1_impossible_of_pins
      Z hB hcard hxb2 hAinSB hpacket
  rcases hrest with hqa2 | hqb2
  · have hpacket : SelectorV3Qa2Packet S Z t := by
      dsimp [SelectorV3Qa2Packet]
      exact ⟨hI3sub, hqa2⟩
    exact S.b3n9m062_selectorShape_v3_q_eq_a2_impossible_of_pins
      Z hB hcard hxb2 hAinSB hpacket
  have hpacket : SelectorV3Qb2Packet S Z t := by
    dsimp [SelectorV3Qb2Packet]
    exact ⟨hI3sub, hqb2⟩
  exact S.b3n9m062_selectorShape_v3_q_eq_b2_impossible_of_pins
    Z hB hcard hxb2 hAinSB hpacket
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit062

-- Original module: Solutions.Batch3N9.Bridge.A1SpineWiring
section Batch3N9Unit063
namespace Batch3N9
open Finset Problem97
open scoped EuclideanGeometry
namespace Problem97
namespace FiniteEndpointShell
theorem mem_C2_of_mem_I2 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {x : ℝ²} (hx : x ∈ S.I2) :
    x ∈ S.CP.C2 :=
  Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
theorem mem_C3_of_mem_I3 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {x : ℝ²} (hx : x ∈ S.I3) :
    x ∈ S.CP.C3 :=
  Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
theorem mem_A_of_mem_I2 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {x : ℝ²} (hx : x ∈ S.I2) :
    x ∈ A :=
  S.CP.C2_subset (mem_C2_of_mem_I2 hx)
theorem not_triangle_of_mem_I2 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {x : ℝ²} (hx : x ∈ S.I2) :
    x ∉ S.triangle.verts := by
  have hxv1 : x ≠ S.triangle.v1 := (Finset.mem_erase.mp hx).1
  have hxv3 : x ≠ S.triangle.v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
  have hxC2 : x ∈ S.CP.C2 := mem_C2_of_mem_I2 hx
  have hxv2 : x ≠ S.triangle.v2 := by
    intro h
    exact S.CP.v2_notin_C2 (h ▸ hxC2)
  simp [Problem97.MoserTriangle.verts, hxv1, hxv2, hxv3]
theorem ne_of_mem_I2_of_mem_I3 {A : Finset ℝ²} {S : FiniteEndpointShell A}
    {x y : ℝ²} (hx : x ∈ S.I2) (hy : y ∈ S.I3) :
    x ≠ y := by
  intro hxy
  have hxA : x ∈ A := mem_A_of_mem_I2 hx
  have hxnon : x ∉ S.triangle.verts := not_triangle_of_mem_I2 hx
  have hxC2 : x ∈ S.CP.C2 := mem_C2_of_mem_I2 hx
  have hxC3 : x ∈ S.CP.C3 := by simpa [hxy] using mem_C3_of_mem_I3 hy
  have hone := S.CP.nonmoser_in_one x hxA hxnon
  by_cases hxC1 : x ∈ S.CP.C1
  · simp [hxC1, hxC2, hxC3] at hone
  · simp [hxC1, hxC2, hxC3] at hone
def FormBv1A2SelectorV2LowerPacketPublic
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r s : ℝ) : Prop :=
  let T := S.witnessClassAt_v2 s
  (Z.a2 : ℝ²) ∈ S.I2 ∧
  S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²) ∧
  T.card = 4 ∧
  S.I2 ⊆ T ∧
  T ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) ∧
  ((T ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
   (T ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²)))
def SelectorV3Qb2PacketPublic
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (t : ℝ) : Prop :=
  let T := S.witnessClassAt_v3 t
  S.I3 ⊆ T ∧
  ∃ p : ℝ²,
    p ∈ ({Z.a1, Z.b1} : Finset ℝ²) ∧
    T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
    T ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²)
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit063

-- Original module: Solutions.Batch3N9.N4d.SmallSReductions
section Batch3N9Unit064
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open EuclideanGeometry
namespace Problem97
theorem nonobtuse_v₃_numerator_nonneg (v₁ v₂ v₃ : ℝ²)
    (h1x : v₁ 0 = 0) (h1y : v₁ 1 = 0) (h2x : v₂ 0 = 1) (h2y : v₂ 1 = 0)
    (hno : 0 ≤ (inner ℝ (v₁ - v₃) (v₂ - v₃) : ℝ)) :
    0 ≤ v₃ 0 ^ 2 - v₃ 0 + v₃ 1 ^ 2 := by
  rw [PiLp.inner_apply] at hno
  simp only [Fin.sum_univ_two, PiLp.sub_apply, h1x, h1y, h2x, h2y,
    RCLike.inner_apply, conj_trivial] at hno
  nlinarith only [hno]
end Problem97
end Batch3N9
end Batch3N9Unit064

-- Original module: Solutions.Batch3N9.N4d.QeqEb2PinClash
section Batch3N9Unit065
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open Finset
namespace Problem97
theorem b3n9m065_dist_sq_coords (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 :=
  Problem97.dist_sq_coord x y
theorem b3n9m065_vec2_c0 (a b : ℝ) : (Problem97.CGN.vec2 a b) 0 = a := by
  simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
theorem b3n9m065_vec2_c1 (a b : ℝ) : (Problem97.CGN.vec2 a b) 1 = b := by
  simp [Problem97.CGN.vec2, EuclideanSpace.single_apply]
theorem b3n9m065_sa2_chart_base_local (p : ℝ²) :
    signedArea2 p (Problem97.CGN.vec2 0 0) (Problem97.CGN.vec2 1 0) = p 1 := by
  simp [Problem97.signedArea2, Problem97.CGN.vec2, EuclideanSpace.single_apply]
  ring
theorem b3n9m065_v3_lt_v3v2_of_mem_I1
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {q : ℝ²}
    (hqI1 : q ∈ S.I1) :
    dist S.triangle.v3 q < dist S.triangle.v3 S.triangle.v2 := by
  classical
  have hqC1 : q ∈ S.CP.C1 :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqI1)
  have hq_ne_v3 : q ≠ S.triangle.v3 :=
    (Finset.mem_erase.mp hqI1).1
  have hq_ne_v2 : q ≠ S.triangle.v2 :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hqI1).2).1
  rcases Problem97.CGN.CGN4g_capData_of_supportCap_oriented
      (A := A) (C := S.CP.C1) (M := S.triangle)
      S.hconv S.hnoncol S.CP.C1_subset
      (fun x hxA => (S.CP.arc_membership x hxA).1)
      S.CP.v2_mem_C1 S.CP.v3_mem_C1 S.Packet S.Packet.inner_at_v1 with
    ⟨m, L, Packet, Hside, Hord, hLC, hEnds⟩
  have hqL : q ∈ Finset.univ.image L.points := by
    rw [hLC]
    exact hqC1
  rcases Finset.mem_image.mp hqL with ⟨i, -, hi⟩
  rcases hEnds with hFirstLast | hLastFirst
  · have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
      intro hi_last
      apply hq_ne_v3
      calc
        q = L.points i := hi.symm
        _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
        _ = S.triangle.v3 := hFirstLast.2
    have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
      have hi_ne_zero : i.val ≠ 0 := by
        intro hi_zero
        have hi_first : i = Problem97.CGN.firstIndex Packet.hm := by
          ext
          simpa [Problem97.CGN.firstIndex] using hi_zero
        apply hq_ne_v2
        calc
          q = L.points i := hi.symm
          _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simp [hi_first]
          _ = S.triangle.v2 := hFirstLast.1
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi_ne_zero
      have hfirst_lt_i : Problem97.CGN.firstIndex Packet.hm < i := by
        rw [Fin.lt_def]
        simpa [Problem97.CGN.firstIndex] using hi_pos
      have hlast_rev_first' :
          (Problem97.CGN.lastIndex Packet.hm).rev = Problem97.CGN.firstIndex Packet.hm := by
        ext
        rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
        simp [Problem97.CGN.firstIndex]
        omega
      rw [Fin.rev_lt_iff]
      simpa [hlast_rev_first'] using hfirst_lt_i
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
        apply hq_ne_v2
        calc
          q = L.points i := hi.symm
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
          _ = S.triangle.v2 := hLastFirst.2
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
theorem b3n9m065_v1_lt_v1v3_of_mem_I2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {p : ℝ²}
    (hpI2 : p ∈ S.I2) :
    dist S.triangle.v1 p < dist S.triangle.v1 S.triangle.v3 := by
  first
  | exact Batch3N9.Problem97.FiniteEndpointShell.b3n9m056_v1_lt_v1v3_of_mem_I2
  | apply Batch3N9.Problem97.FiniteEndpointShell.b3n9m056_v1_lt_v1v3_of_mem_I2 <;> assumption
theorem b3n9m065_v2_lt_v2v1_of_mem_I3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {q : ℝ²}
    (hqI3 : q ∈ S.I3) :
    dist S.triangle.v2 q < dist S.triangle.v2 S.triangle.v1 := by
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
  · have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
      intro hi_last
      apply hq_ne_v2
      calc
        q = L.points i := hi.symm
        _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
        _ = S.triangle.v2 := hFirstLast.2
    have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
      have hi_ne_zero : i.val ≠ 0 := by
        intro hi_zero
        have hi_first : i = Problem97.CGN.firstIndex Packet.hm := by
          ext
          simpa [Problem97.CGN.firstIndex] using hi_zero
        apply hq_ne_v1
        calc
          q = L.points i := hi.symm
          _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simp [hi_first]
          _ = S.triangle.v1 := hFirstLast.1
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi_ne_zero
      have hfirst_lt_i : Problem97.CGN.firstIndex Packet.hm < i := by
        rw [Fin.lt_def]
        simpa [Problem97.CGN.firstIndex] using hi_pos
      have hlast_rev_first' :
          (Problem97.CGN.lastIndex Packet.hm).rev = Problem97.CGN.firstIndex Packet.hm := by
        ext
        rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
        simp [Problem97.CGN.firstIndex]
        omega
      rw [Fin.rev_lt_iff]
      simpa [hlast_rev_first'] using hfirst_lt_i
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
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
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
set_option maxHeartbeats 4000000 in
theorem b3n9m065_frame_circumcenter_facts
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {T : ℝ² → ℝ²} (tau : Problem97.CGN.SimilarityTransportData T)
    (hv1 : T S.triangle.v1 = Problem97.CGN.vec2 0 0)
    (hv2 : T S.triangle.v2 = Problem97.CGN.vec2 1 0)
    (hv3y_pos : 0 < (T S.triangle.v3) 1) :
    (T S.Packet.center) 0 = 1 / 2 ∧ 0 ≤ (T S.Packet.center) 1 ∧
      (tau.scale * S.Packet.radius) ^ 2 = 1 / 4 + (T S.Packet.center) 1 ^ 2 := by
  classical
  have hinner_frame : 0 ≤ (inner ℝ (T S.triangle.v1 - T S.triangle.v3)
      (T S.triangle.v2 - T S.triangle.v3) : ℝ) := by
    have hexp := norm_sub_sq_real (T S.triangle.v1 - T S.triangle.v3)
      (T S.triangle.v2 - T S.triangle.v3)
    have hrw : (T S.triangle.v1 - T S.triangle.v3) - (T S.triangle.v2 - T S.triangle.v3)
        = T S.triangle.v1 - T S.triangle.v2 := by abel
    rw [hrw] at hexp
    have n13 : ‖T S.triangle.v1 - T S.triangle.v3‖
        = tau.scale * dist S.triangle.v1 S.triangle.v3 := by rw [← dist_eq_norm, tau.dist_image]
    have n23 : ‖T S.triangle.v2 - T S.triangle.v3‖
        = tau.scale * dist S.triangle.v2 S.triangle.v3 := by rw [← dist_eq_norm, tau.dist_image]
    have n12 : ‖T S.triangle.v1 - T S.triangle.v2‖
        = tau.scale * dist S.triangle.v1 S.triangle.v2 := by rw [← dist_eq_norm, tau.dist_image]
    rw [n13, n23, n12] at hexp
    have horig := norm_sub_sq_real (S.triangle.v1 - S.triangle.v3)
      (S.triangle.v2 - S.triangle.v3)
    have hrw2 : (S.triangle.v1 - S.triangle.v3) - (S.triangle.v2 - S.triangle.v3)
        = S.triangle.v1 - S.triangle.v2 := by abel
    rw [hrw2] at horig
    have hinner0 : 0 ≤ (inner ℝ (S.triangle.v1 - S.triangle.v3)
        (S.triangle.v2 - S.triangle.v3) : ℝ) := S.Packet.inner_at_v3
    have m13 : ‖S.triangle.v1 - S.triangle.v3‖ = dist S.triangle.v1 S.triangle.v3 :=
      (dist_eq_norm _ _).symm
    have m23 : ‖S.triangle.v2 - S.triangle.v3‖ = dist S.triangle.v2 S.triangle.v3 :=
      (dist_eq_norm _ _).symm
    have m12 : ‖S.triangle.v1 - S.triangle.v2‖ = dist S.triangle.v1 S.triangle.v2 :=
      (dist_eq_norm _ _).symm
    rw [m13, m23, m12] at horig
    have hsc : 0 ≤ tau.scale ^ 2 := sq_nonneg _
    nlinarith only [hexp, hsc, hinner0, horig, mul_nonneg hsc hinner0]
  have h1x : (T S.triangle.v1) 0 = 0 := by rw [hv1, b3n9m065_vec2_c0]
  have h1y : (T S.triangle.v1) 1 = 0 := by rw [hv1, b3n9m065_vec2_c1]
  have h2x : (T S.triangle.v2) 0 = 1 := by rw [hv2, b3n9m065_vec2_c0]
  have h2y : (T S.triangle.v2) 1 = 0 := by rw [hv2, b3n9m065_vec2_c1]
  have hnum : 0 ≤ (T S.triangle.v3) 0 ^ 2 - (T S.triangle.v3) 0 + (T S.triangle.v3) 1 ^ 2 :=
    nonobtuse_v₃_numerator_nonneg _ _ _ h1x h1y h2x h2y hinner_frame
  have hbd1 : dist S.triangle.v1 S.Packet.center = S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.moser_on_boundary_1
  have hbd2 : dist S.triangle.v2 S.Packet.center = S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.moser_on_boundary_2
  have hbd3 : dist S.triangle.v3 S.Packet.center = S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.moser_on_boundary_3
  set R := tau.scale * S.Packet.radius with hR_def
  have hb1sq : dist (T S.triangle.v1) (T S.Packet.center) ^ 2 = R ^ 2 := by
    rw [tau.dist_image, hbd1, hR_def]
  have hb2sq : dist (T S.triangle.v2) (T S.Packet.center) ^ 2 = R ^ 2 := by
    rw [tau.dist_image, hbd2, hR_def]
  have hb3sq : dist (T S.triangle.v3) (T S.Packet.center) ^ 2 = R ^ 2 := by
    rw [tau.dist_image, hbd3, hR_def]
  set Vx := (T S.triangle.v3) 0 with hVx_def
  set Vy := (T S.triangle.v3) 1 with hVy_def
  set ox := (T S.Packet.center) 0 with hox_def
  set Oy := (T S.Packet.center) 1 with hOy_def
  have hVy_pos : 0 < Vy := hv3y_pos
  have e1 : ox ^ 2 + Oy ^ 2 = R ^ 2 := by
    have h := hb1sq
    rw [b3n9m065_dist_sq_coords, h1x, h1y] at h
    simpa [hox_def, hOy_def] using h
  have e2 : (1 - ox) ^ 2 + Oy ^ 2 = R ^ 2 := by
    have h := hb2sq
    rw [b3n9m065_dist_sq_coords, h2x, h2y] at h
    nlinarith only [h]
  have e3 : (Vx - ox) ^ 2 + (Vy - Oy) ^ 2 = R ^ 2 := by
    have h := hb3sq
    rw [b3n9m065_dist_sq_coords] at h
    simpa [hVx_def, hVy_def, hox_def, hOy_def] using h
  clear_value Vx Vy ox Oy R
  have hox : ox = 1 / 2 := by nlinarith only [e1, e2]
  have hOy_nonneg : 0 ≤ Oy := by
    have hmecnum : 2 * Vy * Oy = Vx ^ 2 - Vx + Vy ^ 2 := by nlinarith only [e1, e3, e2, hnum, hox]
    nlinarith only [hnum, hmecnum, hv3y_pos, hVy_pos]
  have hRsq : R ^ 2 = 1 / 4 + Oy ^ 2 := by nlinarith only [e1, e2, hox]
  exact ⟨hox, hOy_nonneg, hRsq⟩
theorem b3n9m065_frame_below_chord
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {x : ℝ²}
    {T : ℝ² → ℝ²} (tau : Problem97.CGN.SimilarityTransportData T)
    (hv1 : T S.triangle.v1 = Problem97.CGN.vec2 0 0)
    (hv2 : T S.triangle.v2 = Problem97.CGN.vec2 1 0)
    (hv3y_pos : 0 < (T S.triangle.v3) 1)
    (hxI3 : x ∈ S.I3) :
    (T x) 1 ≤ 0 := by
  have hxC3 : x ∈ S.CP.C3 :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hxI3).2).2
  have hxA : x ∈ A := S.CP.C3_subset hxC3
  have hopp : Problem97.OnArcOpposite S.triangle.v3 S.triangle.v1 S.triangle.v2 x :=
    ((S.CP.arc_membership x hxA).2.2.mp hxC3)
  unfold Problem97.OnArcOpposite at hopp
  have hp := tau.halfplane_sign x S.triangle.v1 S.triangle.v2
  have hq := tau.halfplane_sign S.triangle.v3 S.triangle.v1 S.triangle.v2
  rw [hv1, hv2, b3n9m065_sa2_chart_base_local] at hp hq
  have hprod : (T x) 1 * (T S.triangle.v3) 1
      = tau.scale ^ 4 *
        (signedArea2 x S.triangle.v1 S.triangle.v2
          * signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2) := by
    have hkey : (T x) 1 * (T S.triangle.v3) 1
        = (tau.orientation ^ 2 * tau.scale ^ 4) *
          (signedArea2 x S.triangle.v1 S.triangle.v2
            * signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2) := by
      rw [hp, hq]; ring
    rw [hkey, tau.orientation_sq, one_mul]
  have hle : (T x) 1 * (T S.triangle.v3) 1 ≤ 0 := by
    rw [hprod]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hopp
  nlinarith only [hle, hv3y_pos]
theorem b3n9m065_frame_disk_pt
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {x : ℝ²}
    {T : ℝ² → ℝ²} (tau : Problem97.CGN.SimilarityTransportData T)
    (hxA : x ∈ A) :
    dist (T x) (T S.Packet.center) ^ 2 ≤ (tau.scale * S.Packet.radius) ^ 2 := by
  have hxdisk : dist x S.Packet.center ≤ S.Packet.radius := by
    rw [dist_eq_norm]; exact S.Packet.disk_contains_A x hxA
  have hle : dist (T x) (T S.Packet.center) ≤ tau.scale * S.Packet.radius := by
    rw [tau.dist_image]
    exact mul_le_mul_of_nonneg_left hxdisk tau.scale_pos.le
  exact pow_le_pow_left₀ dist_nonneg hle 2
set_option maxHeartbeats 1000000 in
theorem pinclash_scalar (s X Y x y Oy : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsdef : (X - 1) ^ 2 + Y ^ 2 = s ^ 2)
    (hcirc : (x - 1) ^ 2 + y ^ 2 = s ^ 2)
    (hY : 0 < Y) (hy : y ≤ 0) (hOy : 0 ≤ Oy)
    (hdisk : (x - 1 / 2) ^ 2 + (y - Oy) ^ 2 ≤ 1 / 4 + Oy ^ 2)
    (hl : 1 < X ^ 2 + Y ^ 2) :
    s ^ 2 < (X - x) ^ 2 + (Y - y) ^ 2 := by
  have hOyy : Oy * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hOy hy
  have hband : x ≤ 1 - s ^ 2 := by nlinarith only [hcirc, hdisk, hOyy]
  have h1x_nonneg : 0 ≤ 1 - x := by nlinarith only [hdisk, hOyy, hband, sq_nonneg s]
  have hsq : (1 - x) ^ 2 ≤ s ^ 2 := by nlinarith only [hcirc, sq_nonneg y]
  have h1x_le_s : 1 - x ≤ s := by nlinarith only [hcirc, hs1, hdisk, hOyy, hs0, hsq, h1x_nonneg]
  have hS2 : 1 - X < s ^ 2 / 2 := by nlinarith only [hsdef, hl]
  have hYy : Y * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hY) hy
  have hip : (X - 1) * (x - 1) + Y * y < s ^ 2 / 2 := by
    rcases le_or_gt X 1 with hX | hX
    · have h1X : 0 ≤ 1 - X := by linarith
      have hb : (1 - X) * (1 - x) ≤ (1 - X) * s :=
        mul_le_mul_of_nonneg_left h1x_le_s h1X
      have hb2 : (1 - X) * s < s ^ 2 / 2 * s := mul_lt_mul_of_pos_right hS2 hs0
      nlinarith only [hYy, hb, hb2, hs0, hs1, mul_pos (mul_pos hs0 hs0) (show (0:ℝ) < 1 - s by linarith)]

    · have hnp : (X - 1) * (x - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      nlinarith only [hYy, hnp, hs0]
  nlinarith only [hsdef, hcirc, hip]
set_option maxHeartbeats 2000000 in
theorem b3n9m065_pinclash_core
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {x₃ : ℝ²}
    (hx3I3 : x₃ ∈ S.I3) (hx3A : x₃ ∈ A)
    (hv2pin : dist S.triangle.v2 x₃ = dist S.triangle.v2 S.triangle.v3)
    (hclash : dist S.triangle.v3 x₃ < dist S.triangle.v3 S.triangle.v2)
    (hell : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3)
    (hs1orig : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v2 S.triangle.v1) :
    False := by
  classical
  obtain ⟨T, tau, hv1, hv2, hv3y_pos⟩ := S.normBase
  obtain ⟨hOx, hOy_nonneg, hRsq⟩ := b3n9m065_frame_circumcenter_facts S tau hv1 hv2 hv3y_pos
  have hyy_le : (T x₃) 1 ≤ 0 := b3n9m065_frame_below_chord S tau hv1 hv2 hv3y_pos hx3I3
  have hdisk_x3 := b3n9m065_frame_disk_pt S tau hx3A
  rw [hRsq] at hdisk_x3
  have h2x : (T S.triangle.v2) 0 = 1 := by rw [hv2, b3n9m065_vec2_c0]
  have h2y : (T S.triangle.v2) 1 = 0 := by rw [hv2, b3n9m065_vec2_c1]
  have h1x : (T S.triangle.v1) 0 = 0 := by rw [hv1, b3n9m065_vec2_c0]
  have h1y : (T S.triangle.v1) 1 = 0 := by rw [hv1, b3n9m065_vec2_c1]
  have hsc_pos : 0 < tau.scale := tau.scale_pos
  have hbase_sq : dist (T S.triangle.v2) (T S.triangle.v1) ^ 2 = 1 := by
    rw [b3n9m065_dist_sq_coords, h2x, h2y, h1x, h1y]; norm_num
  have hbase_one : dist (T S.triangle.v2) (T S.triangle.v1) = 1 := by
    nlinarith only [hbase_sq, dist_nonneg (x := T S.triangle.v2) (y := T S.triangle.v1)]
  have hscale_pin : tau.scale * dist S.triangle.v2 S.triangle.v1 = 1 := by
    rw [← tau.dist_image]; exact hbase_one
  have hd_v2v3 : dist (T S.triangle.v2) (T S.triangle.v3)
      = tau.scale * dist S.triangle.v2 S.triangle.v3 := tau.dist_image _ _
  have hd_v3x3 : dist (T S.triangle.v3) (T x₃)
      = tau.scale * dist S.triangle.v3 x₃ := tau.dist_image _ _
  have hd_v2x3 : dist (T S.triangle.v2) (T x₃)
      = tau.scale * dist S.triangle.v2 x₃ := tau.dist_image _ _
  have hd_v1v3 : dist (T S.triangle.v1) (T S.triangle.v3)
      = tau.scale * dist S.triangle.v1 S.triangle.v3 := tau.dist_image _ _
  have hv23_pos : 0 < dist S.triangle.v2 S.triangle.v3 := dist_pos.mpr S.triangle.v23_ne
  have hsh_pos : 0 < dist (T S.triangle.v2) (T S.triangle.v3) := by
    rw [hd_v2v3]; exact mul_pos hsc_pos hv23_pos
  have hs1 : dist (T S.triangle.v2) (T S.triangle.v3) < 1 := by
    rw [hd_v2v3, ← hscale_pin]; exact mul_lt_mul_of_pos_left hs1orig hsc_pos
  have hpin_frame : dist (T S.triangle.v2) (T x₃) = dist (T S.triangle.v2) (T S.triangle.v3) := by
    rw [hd_v2x3, hv2pin, ← hd_v2v3]
  have hclash_frame : dist (T S.triangle.v3) (T x₃) < dist (T S.triangle.v2) (T S.triangle.v3) := by
    rw [hd_v3x3, hd_v2v3]
    have hd : dist S.triangle.v3 x₃ < dist S.triangle.v2 S.triangle.v3 := by
      rw [dist_comm S.triangle.v2 S.triangle.v3]; exact hclash
    exact mul_lt_mul_of_pos_left hd hsc_pos
  have hv13_gt : (1 : ℝ) < dist (T S.triangle.v1) (T S.triangle.v3) := by
    have hv12 : dist S.triangle.v2 S.triangle.v1 = dist S.triangle.v1 S.triangle.v2 := dist_comm _ _
    rw [hd_v1v3, ← hscale_pin, hv12]; exact mul_lt_mul_of_pos_left hell hsc_pos
  have hsh_lt1_sq : dist (T S.triangle.v2) (T S.triangle.v3) ^ 2 < 1 := by
    nlinarith only [hs1, hsh_pos]
  have hv13_gt_sq : (1 : ℝ) < dist (T S.triangle.v1) (T S.triangle.v3) ^ 2 := by
    nlinarith only [hsh_pos, hv13_gt, hs1]
  have hclash_lt_sq :
      dist (T S.triangle.v3) (T x₃) ^ 2 < dist (T S.triangle.v2) (T S.triangle.v3) ^ 2 := by
    nlinarith only [hsh_pos, hclash_frame, dist_nonneg (x := T S.triangle.v3) (y := T x₃)]
  have hsq_v2v3 := b3n9m065_dist_sq_coords (T S.triangle.v2) (T S.triangle.v3)
  have hsq_v2x3 := b3n9m065_dist_sq_coords (T S.triangle.v2) (T x₃)
  have hsq_v1v3 := b3n9m065_dist_sq_coords (T S.triangle.v1) (T S.triangle.v3)
  have hsq_v3x3 := b3n9m065_dist_sq_coords (T S.triangle.v3) (T x₃)
  have hsq_x3O := b3n9m065_dist_sq_coords (T x₃) (T S.Packet.center)
  rw [h2x, h2y] at hsq_v2v3 hsq_v2x3
  rw [h1x, h1y] at hsq_v1v3
  rw [hOx] at hsq_x3O
  rw [hpin_frame] at hsq_v2x3
  set X := (T S.triangle.v3) 0
  set Y := (T S.triangle.v3) 1
  set xx := (T x₃) 0
  set yy := (T x₃) 1
  set Oy := (T S.Packet.center) 1
  set sh := dist (T S.triangle.v2) (T S.triangle.v3)
  set dv3x3 := dist (T S.triangle.v3) (T x₃)
  set dv1v3 := dist (T S.triangle.v1) (T S.triangle.v3)
  have hsdef : (X - 1) ^ 2 + Y ^ 2 = sh ^ 2 := by linarith [hsq_v2v3]
  have hcirc : (xx - 1) ^ 2 + yy ^ 2 = sh ^ 2 := by linarith [hsq_v2x3]
  have hl : 1 < X ^ 2 + Y ^ 2 := by rw [hsq_v1v3] at hv13_gt_sq; linarith [hv13_gt_sq]
  have hdisk : (xx - 1 / 2) ^ 2 + (yy - Oy) ^ 2 ≤ 1 / 4 + Oy ^ 2 := by
    rw [hsq_x3O] at hdisk_x3; linarith [hdisk_x3]
  have hconc : sh ^ 2 < (X - xx) ^ 2 + (Y - yy) ^ 2 :=
    pinclash_scalar sh X Y xx yy Oy hsh_pos hs1 hsdef hcirc hv3y_pos hyy_le hOy_nonneg hdisk hl
  rw [← hsq_v3x3] at hconc
  linarith [hconc, hclash_lt_sq]
namespace FiniteEndpointShell
theorem b3n9m065_pinclash_from_reps
    {A : Finset ℝ²} {S : FiniteEndpointShell A}
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hA2 : (Z.a2 : ℝ²) ∈ S.I2)
    (hA2eq : S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²))
    (hv3C1 : S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²))
    (hI3sub : S.I3 ⊆ S.witnessClassAt_v3 t)
    {x₃ : ℝ²} (hx3I3 : x₃ ∈ S.I3) (hx3T2 : x₃ ∈ S.witnessClassAt_v2 s)
    {p : ℝ²} (hpI1 : p ∈ S.I1) (hpT3 : p ∈ S.witnessClassAt_v3 t) :
    False := by
  classical
  have hx3A : x₃ ∈ A :=
    S.CP.C3_subset ((Finset.mem_erase.mp (Finset.mem_erase.mp hx3I3).2).2)
  have hv3T2 : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
    have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    rw [← hv3C1] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hd_v2v3 : dist S.triangle.v2 S.triangle.v3 = s := (Finset.mem_filter.mp hv3T2).2
  have hd_v2x3 : dist S.triangle.v2 x₃ = s := (Finset.mem_filter.mp hx3T2).2
  have hv2pin : dist S.triangle.v2 x₃ = dist S.triangle.v2 S.triangle.v3 := by
    rw [hd_v2x3, hd_v2v3]
  have hx3T3 : x₃ ∈ S.witnessClassAt_v3 t := hI3sub hx3I3
  have hd_v3x3 : dist S.triangle.v3 x₃ = t := (Finset.mem_filter.mp hx3T3).2
  have hd_v3p : dist S.triangle.v3 p = t := (Finset.mem_filter.mp hpT3).2
  have hclash : dist S.triangle.v3 x₃ < dist S.triangle.v3 S.triangle.v2 := by
    rw [hd_v3x3, ← hd_v3p]
    exact b3n9m065_v3_lt_v3v2_of_mem_I1 S hpI1
  have hd_v1a2 : dist S.triangle.v1 Z.a2 = r := by
    have ha2T1 : Z.a2 ∈ S.witnessClassAt_v1 r := by
      have hmem : Z.a2 ∈ ({Z.a2} : Finset ℝ²) := by simp
      rw [← hA2eq] at hmem
      exact (Finset.mem_inter.mp hmem).1
    exact (Finset.mem_filter.mp ha2T1).2
  have hd_v1v2 : dist S.triangle.v1 S.triangle.v2 = r := by
    rcases hB with ⟨y, hyI2, hyC2, hv2eq⟩
    have hv2T1 : S.triangle.v2 ∈ S.witnessClassAt_v1 r := by
      have hmem : S.triangle.v2 ∈ ({S.triangle.v2} : Finset ℝ²) := by simp
      rw [← hv2eq] at hmem
      exact (Finset.mem_inter.mp hmem).1
    exact (Finset.mem_filter.mp hv2T1).2
  have hell : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3 := by
    rw [hd_v1v2, ← hd_v1a2]
    exact b3n9m065_v1_lt_v1v3_of_mem_I2 S hA2
  have hs1orig : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v2 S.triangle.v1 := by
    rw [← hv2pin]
    exact b3n9m065_v2_lt_v2v1_of_mem_I3 S hx3I3
  exact b3n9m065_pinclash_core S hx3I3 hx3A hv2pin hclash hell hs1orig
end FiniteEndpointShell
theorem qEqE_b2_column_pinclash_false
    {A : Finset ℝ²} {S : FiniteEndpointShell A}
    (Z : FiniteEndpointShell.ZeroDefectCapLayout S)
    {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hlower : FiniteEndpointShell.FormBv1A2SelectorV2LowerPacketPublic S Z r s)
    (hpacket3 : FiniteEndpointShell.SelectorV3Qb2PacketPublic S Z t) :
    False := by
  classical
  rcases hlower with ⟨hA2, hA2eq, -, -, hv3C1, hC3choice⟩
  rcases hpacket3 with ⟨hI3sub, p, hp, hpC1, -⟩
  have hpI1 : p ∈ S.I1 := by rw [Z.hI1]; exact hp
  have hpT3 : p ∈ S.witnessClassAt_v3 t := by
    have hmem : p ∈ ({p} : Finset ℝ²) := by simp
    rw [← hpC1] at hmem
    exact (Finset.mem_inter.mp hmem).1
  rcases hC3choice with ha3C3 | hb3C3
  · have hx3T2 : (Z.a3 : ℝ²) ∈ S.witnessClassAt_v2 s := by
      have hmem : Z.a3 ∈ ({Z.a3} : Finset ℝ²) := by simp
      rw [← ha3C3] at hmem
      exact (Finset.mem_inter.mp hmem).1
    have hx3I3 : (Z.a3 : ℝ²) ∈ S.I3 := by rw [Z.hI3]; simp
    exact FiniteEndpointShell.b3n9m065_pinclash_from_reps Z hB hA2 hA2eq hv3C1 hI3sub
      hx3I3 hx3T2 hpI1 hpT3
  · have hx3T2 : (Z.b3 : ℝ²) ∈ S.witnessClassAt_v2 s := by
      have hmem : Z.b3 ∈ ({Z.b3} : Finset ℝ²) := by simp
      rw [← hb3C3] at hmem
      exact (Finset.mem_inter.mp hmem).1
    have hx3I3 : (Z.b3 : ℝ²) ∈ S.I3 := by rw [Z.hI3]; simp
    exact FiniteEndpointShell.b3n9m065_pinclash_from_reps Z hB hA2 hA2eq hv3C1 hI3sub
      hx3I3 hx3T2 hpI1 hpT3
end Problem97
end Batch3N9
end Batch3N9Unit065

-- Original module: Solutions.Batch3N9.N4d.ExcludesFormBv1
section Batch3N9Unit066
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
theorem exists_capLayout
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Nonempty (ZeroDefectCapLayout S) :=
  ⟨(p2mCoreSupport S).layout⟩
end FiniteEndpointShell
theorem b3n9m066_v1_lt_v1v3_of_mem_I2_local
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
        _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simp [hi_first]
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
      have hi_lt_top : i.val < m := i.is_lt
      have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
        intro hi_last
        apply hp_ne_v3
        calc
          p = L.points i := hi.symm
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
          _ = S.triangle.v3 := hLastFirst.2
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
theorem b3n9m066_v1_lt_v1v2_of_mem_I3_local
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
        _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
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
      have hi_le_pred : i.val ≤ m - 1 := Nat.le_pred_of_lt hi_lt_top
      exact lt_of_le_of_ne hi_le_pred hi_ne_top
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
      rw [Problem97.CGN.lastIndex_val]
      have hi_lt_top : i.val < m := i.is_lt
      have hi_pos : 0 < i.val := by
        apply Nat.pos_of_ne_zero
        intro hi_zero
        apply hi_ne_first
        ext
        simpa [Problem97.CGN.firstIndex] using hi_zero
      have h1 : 1 < i.val + 1 := Nat.succ_lt_succ hi_pos
      have hm1 : 1 < m := lt_of_lt_of_le h1 (Nat.succ_le_of_lt hi_lt_top)
      simpa [Fin.val_rev] using (Nat.sub_lt_sub_left hm1 h1)
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
      hi, hLastFirst.1, hLastFirst.2, hlast_rev_first] using hlt
theorem b3n9m066_v2_lt_v2v1_of_mem_I3_local
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {q : ℝ²}
    (hqI3 : q ∈ S.I3) :
    dist S.triangle.v2 q < dist S.triangle.v2 S.triangle.v1 := by
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
  · have hi_ne_last : i ≠ Problem97.CGN.lastIndex Packet.hm := by
      intro hi_last
      apply hq_ne_v2
      calc
        q = L.points i := hi.symm
        _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
        _ = S.triangle.v2 := hFirstLast.2
    have hi_rev_lt_last : i.rev < Problem97.CGN.lastIndex Packet.hm := by
      have hi_ne_zero : i.val ≠ 0 := by
        intro hi_zero
        have hi_first : i = Problem97.CGN.firstIndex Packet.hm := by
          ext
          simpa [Problem97.CGN.firstIndex] using hi_zero
        apply hq_ne_v1
        calc
          q = L.points i := hi.symm
          _ = L.points (Problem97.CGN.firstIndex Packet.hm) := by simp [hi_first]
          _ = S.triangle.v1 := hFirstLast.1
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi_ne_zero
      have hfirst_lt_i : Problem97.CGN.firstIndex Packet.hm < i := by
        rw [Fin.lt_def]
        simpa [Problem97.CGN.firstIndex] using hi_pos
      have hlast_rev_first' :
          (Problem97.CGN.lastIndex Packet.hm).rev = Problem97.CGN.firstIndex Packet.hm := by
        ext
        rw [Fin.val_rev, Problem97.CGN.lastIndex_val]
        simp [Problem97.CGN.firstIndex]
        omega
      rw [Fin.rev_lt_iff]
      simpa [hlast_rev_first'] using hfirst_lt_i
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
          _ = L.points (Problem97.CGN.lastIndex Packet.hm) := by simp [hi_last]
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
theorem FiniteEndpointShell.n4d_bB_4_q_eq_E_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hB2 : (Z.b2 : ℝ²) ∈ S.I2)
    (hb2eq : S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²))
    (hI2sub : S.I2 ⊆ S.witnessClassAt_v2 s)
    (hC1eq : S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²))
    (hC3eq :
      (S.witnessClassAt_v2 s ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
      (S.witnessClassAt_v2 s ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²)))
    (hC2eq3 : S.witnessClassAt_v3 t ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²))
    (hI3sub : S.I3 ⊆ S.witnessClassAt_v3 t) :
    False := by
  classical
  rcases hB with ⟨_, _, _, hv2eq⟩
  let T : Finset ℝ² := S.witnessClassAt_v2 s
  have hv3T : S.triangle.v3 ∈ T := by
    have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    rw [← hC1eq] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hqset : (Z.a3 : ℝ²) ∈ T ∩ S.CP.C3 ∨ (Z.b3 : ℝ²) ∈ T ∩ S.CP.C3 := by
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
    rcases hqset with hqa3 | hqb3
    · refine ⟨Z.a3, ?_, ?_⟩
      · rw [Z.hI3]
        simp
      · exact (Finset.mem_inter.mp hqa3).1
    · refine ⟨Z.b3, ?_, ?_⟩
      · rw [Z.hI3]
        simp
      · exact (Finset.mem_inter.mp hqb3).1
  have hb2T1 : Z.b2 ∈ S.witnessClassAt_v1 r := by
    have hb2mem : Z.b2 ∈ ({Z.b2} : Finset ℝ²) := by simp
    rw [← hb2eq] at hb2mem
    exact (Finset.mem_inter.mp hb2mem).1
  have hv2T1 : S.triangle.v2 ∈ S.witnessClassAt_v1 r := by
    have hv2mem : S.triangle.v2 ∈ ({S.triangle.v2} : Finset ℝ²) := by simp
    rw [← hv2eq] at hv2mem
    exact (Finset.mem_inter.mp hv2mem).1
  have hAE : dist S.triangle.v1 Z.b2 = dist S.triangle.v1 S.triangle.v2 := by
    have hb2r : dist S.triangle.v1 Z.b2 = r := by
      simpa using (Finset.mem_filter.mp hb2T1).2
    have hv2r : dist S.triangle.v1 S.triangle.v2 = r := by
      simpa using (Finset.mem_filter.mp hv2T1).2
    rw [hb2r, hv2r]
  have hBD : dist S.triangle.v2 S.triangle.v3 = dist S.triangle.v2 Z.b2 := by
    have hb2T2 : Z.b2 ∈ T := hI2sub hB2
    have hv3r : dist S.triangle.v2 S.triangle.v3 = s := by
      simpa [T] using (Finset.mem_filter.mp hv3T).2
    have hb2r : dist S.triangle.v2 Z.b2 = s := by
      simpa [T] using (Finset.mem_filter.mp hb2T2).2
    rw [hv3r, hb2r]
  have hBq : dist S.triangle.v2 q = dist S.triangle.v2 Z.b2 := by
    have hqT2' : q ∈ T := hqT2
    have hqr : dist S.triangle.v2 q = s := by
      simpa [T] using (Finset.mem_filter.mp hqT2').2
    have hb2r : dist S.triangle.v2 Z.b2 = s := by
      have hb2T2 : Z.b2 ∈ T := hI2sub hB2
      simpa [T] using (Finset.mem_filter.mp hb2T2).2
    rw [hqr, hb2r]
  have hDq : dist S.triangle.v3 q = dist S.triangle.v3 Z.b2 := by
    have hqT3 : q ∈ S.witnessClassAt_v3 t := hI3sub hqI3
    have hqr : dist S.triangle.v3 q = t := by
      simpa using (Finset.mem_filter.mp hqT3).2
    have hb2T3 : Z.b2 ∈ S.witnessClassAt_v3 t := by
      have hb2mem : Z.b2 ∈ ({Z.b2} : Finset ℝ²) := by simp
      rw [← hC2eq3] at hb2mem
      exact (Finset.mem_inter.mp hb2mem).1
    have hb2r : dist S.triangle.v3 Z.b2 = t := by
      simpa using (Finset.mem_filter.mp hb2T3).2
    rw [hqr, hb2r]
  have hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3 := by
    simpa [hAE] using (b3n9m066_v1_lt_v1v3_of_mem_I2_local S hB2)
  have hEside :
      0 < signedArea2 Z.b2 S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 :=
    (p2mCoreSupport S).c2_vertex_same_open_side_as_v3 hB2
  have hqE : q ≠ Z.b2 := by
    intro hqb2
    have hlt := b3n9m066_v1_lt_v1v2_of_mem_I3_local S hqI3
    rw [hqb2, hAE] at hlt
    exact lt_irrefl _ hlt
  exact (p2mBranchSupport S Z).qEqE_row_impossible_of_reflection hqI3 hAE hBD hBq hDq hlong hEside hqE
theorem FiniteEndpointShell.n4d_bB_5_q_eq_C_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hB : S.IsFormB_v1 r)
    (hB2 : (Z.b2 : ℝ²) ∈ S.I2)
    (hb2eq : S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²))
    (hI2sub : S.I2 ⊆ S.witnessClassAt_v2 s)
    (hC1eq : S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²))
    (hC3eq :
      (S.witnessClassAt_v2 s ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
      (S.witnessClassAt_v2 s ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²)))
    (hpacket : SelectorV3Qa2Packet S Z t) :
    False := by
  classical
  rcases hB with ⟨_, _, _, hv2eq⟩
  have hb2T1 : Z.b2 ∈ S.witnessClassAt_v1 r := by
    have hb2mem : Z.b2 ∈ ({Z.b2} : Finset ℝ²) := by simp
    rw [← hb2eq] at hb2mem
    exact (Finset.mem_inter.mp hb2mem).1
  have hv2T1 : S.triangle.v2 ∈ S.witnessClassAt_v1 r := by
    have hv2mem : S.triangle.v2 ∈ ({S.triangle.v2} : Finset ℝ²) := by simp
    rw [← hv2eq] at hv2mem
    exact (Finset.mem_inter.mp hv2mem).1
  have hAEb2 : dist S.triangle.v1 Z.b2 = dist S.triangle.v1 S.triangle.v2 := by
    have hb2r : dist S.triangle.v1 Z.b2 = r := by
      simpa using (Finset.mem_filter.mp hb2T1).2
    have hv2r : dist S.triangle.v1 S.triangle.v2 = r := by
      simpa using (Finset.mem_filter.mp hv2T1).2
    rw [hb2r, hv2r]
  have hlong : dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3 := by
    simpa [hAEb2] using (b3n9m066_v1_lt_v1v3_of_mem_I2_local S hB2)
  have hA2I2 : Z.a2 ∈ S.I2 := by
    rw [Z.hI2]
    simp
  have hA2C2 : Z.a2 ∈ S.CP.C2 := by
    unfold Problem97.FiniteEndpointShell.I2 at hA2I2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2I2).2).2
  have hA2T2 : Z.a2 ∈ S.witnessClassAt_v2 s := hI2sub hA2I2
  have hEside :
      0 < signedArea2 Z.a2 S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 :=
    (p2mCoreSupport S).c2_vertex_same_open_side_as_v3 hA2I2
  rcases hpacket with ⟨hI3sub, hpacket⟩
  rcases hpacket with ⟨p, hpnamed, hpC1, hpC2⟩
  have hA2T3 : Z.a2 ∈ S.witnessClassAt_v3 t := by
    have hmem : Z.a2 ∈ ({Z.a2} : Finset ℝ²) := by simp
    rw [← hpC2] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hsmall : dist S.triangle.v2 S.triangle.v3 < dist S.triangle.v1 S.triangle.v2 := by
    rcases hC3eq with hqa3 | hqb3
    · have hqI3 : Z.a3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqT2 : Z.a3 ∈ S.witnessClassAt_v2 s := by
        have hmem : Z.a3 ∈ ({Z.a3} : Finset ℝ²) := by simp
        rw [← hqa3] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hv3T2 : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
        have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
        rw [← hC1eq] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hq_lt_base : dist S.triangle.v2 Z.a3 < dist S.triangle.v2 S.triangle.v1 :=
        b3n9m066_v2_lt_v2v1_of_mem_I3_local S hqI3
      have hqrad : dist S.triangle.v2 Z.a3 = s := by
        simpa using (Finset.mem_filter.mp hqT2).2
      have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
        simpa using (Finset.mem_filter.mp hv3T2).2
      calc
        dist S.triangle.v2 S.triangle.v3 = dist S.triangle.v2 Z.a3 := by
          rw [hv3rad, hqrad]
        _ < dist S.triangle.v2 S.triangle.v1 := hq_lt_base
        _ = dist S.triangle.v1 S.triangle.v2 := by rw [dist_comm]
    · have hqI3 : Z.b3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqT2 : Z.b3 ∈ S.witnessClassAt_v2 s := by
        have hmem : Z.b3 ∈ ({Z.b3} : Finset ℝ²) := by simp
        rw [← hqb3] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hv3T2 : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
        have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
        rw [← hC1eq] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hq_lt_base : dist S.triangle.v2 Z.b3 < dist S.triangle.v2 S.triangle.v1 :=
        b3n9m066_v2_lt_v2v1_of_mem_I3_local S hqI3
      have hqrad : dist S.triangle.v2 Z.b3 = s := by
        simpa using (Finset.mem_filter.mp hqT2).2
      have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
        simpa using (Finset.mem_filter.mp hv3T2).2
      calc
        dist S.triangle.v2 S.triangle.v3 = dist S.triangle.v2 Z.b3 := by
          rw [hv3rad, hqrad]
        _ < dist S.triangle.v2 S.triangle.v1 := hq_lt_base
        _ = dist S.triangle.v1 S.triangle.v2 := by rw [dist_comm]
  have hA2ne_base : dist S.triangle.v1 Z.a2 ≠ dist S.triangle.v1 S.triangle.v2 := by
    intro hEq
    have hA2neqb2 : Z.a2 ≠ Z.b2 := by
      intro hEq2
      have hcard : ({Z.a2, Z.b2} : Finset ℝ²).card = 2 := by
        simpa [Z.hI2] using (p2mCoreSupport S).I2_card_eq_two
      rw [hEq2] at hcard
      simp at hcard
    have hA2T1 : Z.a2 ∈ S.witnessClassAt_v1 r := by
      have hA2r : dist S.triangle.v1 Z.a2 = r := by
        rw [hEq, (Finset.mem_filter.mp hv2T1).2]
      change Z.a2 ∈ A.filter (fun x => dist S.triangle.v1 x = r)
      exact Finset.mem_filter.mpr ⟨S.CP.C2_subset hA2C2, hA2r⟩
    have hA2inter : Z.a2 ∈ S.witnessClassAt_v1 r ∩ S.CP.C2 := by
      exact Finset.mem_inter.mpr ⟨hA2T1, hA2C2⟩
    rw [hb2eq] at hA2inter
    have hEq2 : Z.a2 = Z.b2 := by
      simpa using hA2inter
    exact hA2neqb2 hEq2
  have hA3neqb3 : Z.a3 ≠ Z.b3 := by
    intro hEq
    have hcard : ({Z.a3, Z.b3} : Finset ℝ²).card = 2 := by
      simpa [Z.hI3] using (p2mCoreSupport S).I3_card_eq_two
    rw [hEq] at hcard
    simp at hcard
  rcases lt_or_gt_of_ne hA2ne_base with hAElt | hAEgt
  · rcases hC3eq with hqa3 | hqb3
    · have hqI3 : Z.a3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqsI3 : Z.b3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqT2 : Z.a3 ∈ S.witnessClassAt_v2 s := by
        have hmem : Z.a3 ∈ ({Z.a3} : Finset ℝ²) := by simp
        rw [← hqa3] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hv3T2 : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
        have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
        rw [← hC1eq] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hBq : dist S.triangle.v2 Z.a3 = dist S.triangle.v2 S.triangle.v3 := by
        have hqrad : dist S.triangle.v2 Z.a3 = s := by
          simpa using (Finset.mem_filter.mp hqT2).2
        have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
          simpa using (Finset.mem_filter.mp hv3T2).2
        rw [hqrad, hv3rad]
      have hqT3 : Z.a3 ∈ S.witnessClassAt_v3 t := hI3sub hqI3
      have hqsT3 : Z.b3 ∈ S.witnessClassAt_v3 t := hI3sub hqsI3
      have hDqs : dist S.triangle.v3 Z.b3 = dist S.triangle.v3 Z.a3 := by
        have hqrad3 : dist S.triangle.v3 Z.a3 = t := by
          simpa using (Finset.mem_filter.mp hqT3).2
        have hqsrad3 : dist S.triangle.v3 Z.b3 = t := by
          simpa using (Finset.mem_filter.mp hqsT3).2
        rw [hqsrad3, hqrad3]
      have hBE : dist S.triangle.v2 Z.a2 = dist S.triangle.v2 S.triangle.v3 := by
        have hErad : dist S.triangle.v2 Z.a2 = s := by
          simpa using (Finset.mem_filter.mp hA2T2).2
        have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
          simpa using (Finset.mem_filter.mp hv3T2).2
        rw [hErad, hv3rad]
      have hDE : dist S.triangle.v3 Z.a2 = dist S.triangle.v3 Z.a3 := by
        have hErad3 : dist S.triangle.v3 Z.a2 = t := by
          simpa using (Finset.mem_filter.mp hA2T3).2
        have hqrad3 : dist S.triangle.v3 Z.a3 = t := by
          simpa using (Finset.mem_filter.mp hqT3).2
        rw [hErad3, hqrad3]
      have hqE : Z.a3 ≠ Z.a2 := by
        intro hEq
        exact (S.ne_of_mem_I2_of_mem_I3 hA2I2 hqI3) hEq.symm
      have hq_ne_qs : Z.a3 ≠ Z.b3 := hA3neqb3
      have hcap_opp :=
        (p2mCoreSupport S).qEqE_capOrder_opposite hqI3 hqsI3 hq_ne_qs
      exact (p2mBranchSupport S Z).qEqE_lowerArc_impossible (q := Z.a3) (qs := Z.b3) (E := Z.a2)
        hqI3 hqsI3 hDqs hBq hBE hDE hsmall hlong hAElt hEside hqE hcap_opp
    · have hqI3 : Z.b3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqsI3 : Z.a3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqT2 : Z.b3 ∈ S.witnessClassAt_v2 s := by
        have hmem : Z.b3 ∈ ({Z.b3} : Finset ℝ²) := by simp
        rw [← hqb3] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hv3T2 : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
        have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
        rw [← hC1eq] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hBq : dist S.triangle.v2 Z.b3 = dist S.triangle.v2 S.triangle.v3 := by
        have hqrad : dist S.triangle.v2 Z.b3 = s := by
          simpa using (Finset.mem_filter.mp hqT2).2
        have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
          simpa using (Finset.mem_filter.mp hv3T2).2
        rw [hqrad, hv3rad]
      have hqT3 : Z.b3 ∈ S.witnessClassAt_v3 t := hI3sub hqI3
      have hqsT3 : Z.a3 ∈ S.witnessClassAt_v3 t := hI3sub hqsI3
      have hDqs : dist S.triangle.v3 Z.a3 = dist S.triangle.v3 Z.b3 := by
        have hqrad3 : dist S.triangle.v3 Z.b3 = t := by
          simpa using (Finset.mem_filter.mp hqT3).2
        have hqsrad3 : dist S.triangle.v3 Z.a3 = t := by
          simpa using (Finset.mem_filter.mp hqsT3).2
        rw [hqsrad3, hqrad3]
      have hBE : dist S.triangle.v2 Z.a2 = dist S.triangle.v2 S.triangle.v3 := by
        have hErad : dist S.triangle.v2 Z.a2 = s := by
          simpa using (Finset.mem_filter.mp hA2T2).2
        have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
          simpa using (Finset.mem_filter.mp hv3T2).2
        rw [hErad, hv3rad]
      have hDE : dist S.triangle.v3 Z.a2 = dist S.triangle.v3 Z.b3 := by
        have hErad3 : dist S.triangle.v3 Z.a2 = t := by
          simpa using (Finset.mem_filter.mp hA2T3).2
        have hqrad3 : dist S.triangle.v3 Z.b3 = t := by
          simpa using (Finset.mem_filter.mp hqT3).2
        rw [hErad3, hqrad3]
      have hqE : Z.b3 ≠ Z.a2 := by
        intro hEq
        exact (S.ne_of_mem_I2_of_mem_I3 hA2I2 hqI3) hEq.symm
      have hq_ne_qs : Z.b3 ≠ Z.a3 := hA3neqb3.symm
      have hcap_opp :=
        (p2mCoreSupport S).qEqE_capOrder_opposite hqI3 hqsI3 hq_ne_qs
      exact (p2mBranchSupport S Z).qEqE_lowerArc_impossible (q := Z.b3) (qs := Z.a3) (E := Z.a2)
        hqI3 hqsI3 hDqs hBq hBE hDE hsmall hlong hAElt hEside hqE hcap_opp
  · rcases hC3eq with hqa3 | hqb3
    · have hqI3 : Z.a3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqsI3 : Z.b3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqT2 : Z.a3 ∈ S.witnessClassAt_v2 s := by
        have hmem : Z.a3 ∈ ({Z.a3} : Finset ℝ²) := by simp
        rw [← hqa3] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hv3T2 : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
        have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
        rw [← hC1eq] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hBq : dist S.triangle.v2 Z.a3 = dist S.triangle.v2 S.triangle.v3 := by
        have hqrad : dist S.triangle.v2 Z.a3 = s := by
          simpa using (Finset.mem_filter.mp hqT2).2
        have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
          simpa using (Finset.mem_filter.mp hv3T2).2
        rw [hqrad, hv3rad]
      have hqT3 : Z.a3 ∈ S.witnessClassAt_v3 t := hI3sub hqI3
      have hqsT3 : Z.b3 ∈ S.witnessClassAt_v3 t := hI3sub hqsI3
      have hDqs : dist S.triangle.v3 Z.b3 = dist S.triangle.v3 Z.a3 := by
        have hqrad3 : dist S.triangle.v3 Z.a3 = t := by
          simpa using (Finset.mem_filter.mp hqT3).2
        have hqsrad3 : dist S.triangle.v3 Z.b3 = t := by
          simpa using (Finset.mem_filter.mp hqsT3).2
        rw [hqsrad3, hqrad3]
      have hBE : dist S.triangle.v2 Z.a2 = dist S.triangle.v2 S.triangle.v3 := by
        have hErad : dist S.triangle.v2 Z.a2 = s := by
          simpa using (Finset.mem_filter.mp hA2T2).2
        have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
          simpa using (Finset.mem_filter.mp hv3T2).2
        rw [hErad, hv3rad]
      have hDE : dist S.triangle.v3 Z.a2 = dist S.triangle.v3 Z.a3 := by
        have hErad3 : dist S.triangle.v3 Z.a2 = t := by
          simpa using (Finset.mem_filter.mp hA2T3).2
        have hqrad3 : dist S.triangle.v3 Z.a3 = t := by
          simpa using (Finset.mem_filter.mp hqT3).2
        rw [hErad3, hqrad3]
      have hqE : Z.a3 ≠ Z.a2 := by
        intro hEq
        exact (S.ne_of_mem_I2_of_mem_I3 hA2I2 hqI3) hEq.symm
      have hq_ne_qs : Z.a3 ≠ Z.b3 := hA3neqb3
      have hcap_opp :=
        (p2mCoreSupport S).qEqE_capOrder_opposite hqI3 hqsI3 hq_ne_qs
      exact (p2mBranchSupport S Z).qEqE_lowerArc_impossible_flipped (q := Z.a3) (qs := Z.b3) (E := Z.a2)
        hqI3 hqsI3 hDqs hBq hBE hDE hsmall hlong hAEgt hA2C2 hEside hqE hcap_opp
    · have hqI3 : Z.b3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqsI3 : Z.a3 ∈ S.I3 := by
        rw [Z.hI3]
        simp
      have hqT2 : Z.b3 ∈ S.witnessClassAt_v2 s := by
        have hmem : Z.b3 ∈ ({Z.b3} : Finset ℝ²) := by simp
        rw [← hqb3] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hv3T2 : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
        have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
        rw [← hC1eq] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hBq : dist S.triangle.v2 Z.b3 = dist S.triangle.v2 S.triangle.v3 := by
        have hqrad : dist S.triangle.v2 Z.b3 = s := by
          simpa using (Finset.mem_filter.mp hqT2).2
        have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
          simpa using (Finset.mem_filter.mp hv3T2).2
        rw [hqrad, hv3rad]
      have hqT3 : Z.b3 ∈ S.witnessClassAt_v3 t := hI3sub hqI3
      have hqsT3 : Z.a3 ∈ S.witnessClassAt_v3 t := hI3sub hqsI3
      have hDqs : dist S.triangle.v3 Z.a3 = dist S.triangle.v3 Z.b3 := by
        have hqrad3 : dist S.triangle.v3 Z.b3 = t := by
          simpa using (Finset.mem_filter.mp hqT3).2
        have hqsrad3 : dist S.triangle.v3 Z.a3 = t := by
          simpa using (Finset.mem_filter.mp hqsT3).2
        rw [hqsrad3, hqrad3]
      have hBE : dist S.triangle.v2 Z.a2 = dist S.triangle.v2 S.triangle.v3 := by
        have hErad : dist S.triangle.v2 Z.a2 = s := by
          simpa using (Finset.mem_filter.mp hA2T2).2
        have hv3rad : dist S.triangle.v2 S.triangle.v3 = s := by
          simpa using (Finset.mem_filter.mp hv3T2).2
        rw [hErad, hv3rad]
      have hDE : dist S.triangle.v3 Z.a2 = dist S.triangle.v3 Z.b3 := by
        have hErad3 : dist S.triangle.v3 Z.a2 = t := by
          simpa using (Finset.mem_filter.mp hA2T3).2
        have hqrad3 : dist S.triangle.v3 Z.b3 = t := by
          simpa using (Finset.mem_filter.mp hqT3).2
        rw [hErad3, hqrad3]
      have hqE : Z.b3 ≠ Z.a2 := by
        intro hEq
        exact (S.ne_of_mem_I2_of_mem_I3 hA2I2 hqI3) hEq.symm
      have hq_ne_qs : Z.b3 ≠ Z.a3 := hA3neqb3.symm
      have hcap_opp :=
        (p2mCoreSupport S).qEqE_capOrder_opposite hqI3 hqsI3 hq_ne_qs
      exact (p2mBranchSupport S Z).qEqE_lowerArc_impossible_flipped (q := Z.b3) (qs := Z.a3) (E := Z.a2)
        hqI3 hqsI3 hDqs hBq hBE hDE hsmall hlong hAEgt hA2C2 hEside hqE hcap_opp
theorem FiniteEndpointShell.N4dExcludesFormB_v1_proof
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.N4dExcludesFormB_v1 := by
  classical
  intro r hr hcard hesc hB
  obtain ⟨Z⟩ := S.exists_capLayout
  rcases (p2mCoreSupport S).formB_v1_split Z hB with ⟨ha2, hxa2⟩ | ⟨hb2, hxb2⟩
  · rcases (p2mCoreSupport S).selectorShape_v2_split Z with ⟨s, hs, hsplit2⟩
    rcases hsplit2 with ⟨hTcard2, hI2sub, hcases2⟩
    rcases hcases2 with hqv1 | hlower
    · have hB2 : Xb2Pin S (Z.swapI2) r := by
        refine ⟨?_, ?_⟩
        · simpa [FiniteEndpointShell.ZeroDefectCapLayout.swapI2] using ha2
        · simpa [FiniteEndpointShell.ZeroDefectCapLayout.swapI2] using hxa2
      have hAinSB : AInSBPin S (Z.swapI2) s := by
        refine ⟨hs, hTcard2, hI2sub, ?_⟩
        simpa [SelectorV2Qv1Packet, FiniteEndpointShell.ZeroDefectCapLayout.swapI2] using hqv1
      exact S.n4d_bB1_impossible (Z := Z.swapI2) hB hcard hB2 hAinSB
    · rcases hlower with ha3 | hb3
      · rcases ha3 with ⟨p2, hp2, hp2C1, ha3C3⟩
        have hp2v3 : S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) :=
          S.selectorShape_v2_lower_forces_v3 Z hr hs hcard hB ha2 hxa2 hI2sub hp2 hp2C1
        have hlowerPacket : FiniteEndpointShell.FormBv1A2SelectorV2LowerPacket S Z r s := by
          exact ⟨ha2, hxa2, hTcard2, hI2sub, hp2v3, Or.inl ha3C3⟩
        rcases (p2mCoreSupport S).selectorShape_v3_split Z with ⟨t, ht, hsplit3⟩
        rcases hsplit3 with ⟨_, hI3sub, hcases3⟩
        rcases hcases3 with hqv1 | hrest
        · exact (p2mBranchSupport S Z).n4d_bA_2_q_eq_v1_impossible hB hlowerPacket hqv1
        · rcases hrest with hqa2 | hqb2
          · exact (p2mBranchSupport S Z).n4d_bA_2_q_eq_C_impossible hB hlowerPacket ⟨hI3sub, hqa2⟩
          · rcases hqb2 with ⟨p3, hp3, hp3C1, hb2C2⟩
            rcases Finset.mem_insert.mp hp3 with hpa1 | hp3
            · exact Problem97.qEqE_b2_column_pinclash_false Z hB
                (by
                  simpa [FiniteEndpointShell.FormBv1A2SelectorV2LowerPacketPublic,
                    FiniteEndpointShell.FormBv1A2SelectorV2LowerPacket] using hlowerPacket)
                ⟨hI3sub, p3, by simpa [hpa1] using hp3, hp3C1, hb2C2⟩
            rcases Finset.mem_insert.mp hp3 with hpb1 | hpv2
            · exact Problem97.qEqE_b2_column_pinclash_false Z hB
                (by
                  simpa [FiniteEndpointShell.FormBv1A2SelectorV2LowerPacketPublic,
                    FiniteEndpointShell.FormBv1A2SelectorV2LowerPacket] using hlowerPacket)
                ⟨hI3sub, p3, by simpa [hpb1] using hp3, hp3C1, hb2C2⟩
            · have hpv2' : p3 = S.triangle.v2 := by simpa using hpv2
              rw [hpv2'] at hp3C1
              exact S.pEqB_column_impossible Z hB hlowerPacket
                (by
                  simpa [FiniteEndpointShell.SelectorV3PeqBPacket] using
                    (show FiniteEndpointShell.SelectorV3Pv2Packet S Z t from
                      ⟨hI3sub, hp3C1, Or.inr hb2C2⟩))
      · rcases hb3 with ⟨p2, hp2, hp2C1, hb3C3⟩
        have hp2v3 : S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) :=
          S.selectorShape_v2_lower_forces_v3 Z hr hs hcard hB ha2 hxa2 hI2sub hp2 hp2C1
        have hlowerPacket : FiniteEndpointShell.FormBv1A2SelectorV2LowerPacket S Z r s := by
          exact ⟨ha2, hxa2, hTcard2, hI2sub, hp2v3, Or.inr hb3C3⟩
        rcases (p2mCoreSupport S).selectorShape_v3_split Z with ⟨t, ht, hsplit3⟩
        rcases hsplit3 with ⟨_, hI3sub, hcases3⟩
        rcases hcases3 with hqv1 | hrest
        · exact (p2mBranchSupport S Z).n4d_bA_2_q_eq_v1_impossible hB hlowerPacket hqv1
        · rcases hrest with hqa2 | hqb2
          · exact (p2mBranchSupport S Z).n4d_bA_2_q_eq_C_impossible hB hlowerPacket ⟨hI3sub, hqa2⟩
          · rcases hqb2 with ⟨p3, hp3, hp3C1, hb2C2⟩
            rcases Finset.mem_insert.mp hp3 with hpa1 | hp3
            · exact Problem97.qEqE_b2_column_pinclash_false Z hB
                (by
                  simpa [FiniteEndpointShell.FormBv1A2SelectorV2LowerPacketPublic,
                    FiniteEndpointShell.FormBv1A2SelectorV2LowerPacket] using hlowerPacket)
                ⟨hI3sub, p3, by simpa [hpa1] using hp3, hp3C1, hb2C2⟩
            rcases Finset.mem_insert.mp hp3 with hpb1 | hpv2
            · exact Problem97.qEqE_b2_column_pinclash_false Z hB
                (by
                  simpa [FiniteEndpointShell.FormBv1A2SelectorV2LowerPacketPublic,
                    FiniteEndpointShell.FormBv1A2SelectorV2LowerPacket] using hlowerPacket)
                ⟨hI3sub, p3, by simpa [hpb1] using hp3, hp3C1, hb2C2⟩
            · have hpv2' : p3 = S.triangle.v2 := by simpa using hpv2
              rw [hpv2'] at hp3C1
              exact S.pEqB_column_impossible Z hB hlowerPacket
                (by
                  simpa [FiniteEndpointShell.SelectorV3PeqBPacket] using
                    (show FiniteEndpointShell.SelectorV3Pv2Packet S Z t from
                      ⟨hI3sub, hp3C1, Or.inr hb2C2⟩))
  · rcases (p2mCoreSupport S).selectorShape_v2_split Z with ⟨s, hs, hsplit2⟩
    rcases hsplit2 with ⟨hTcard2, hI2sub, hcases2⟩
    rcases hcases2 with hqv1 | hlower
    · exact S.n4d_bB1_impossible Z hB hcard ⟨hb2, hxb2⟩ ⟨hs, hTcard2, hI2sub, hqv1⟩
    · rcases hlower with hqa3 | hqb3
      · rcases hqa3 with ⟨p2, hp2, hp2C1, ha3C3⟩
        have hB2 : (Z.b2 : ℝ²) ∈ S.I2 := hb2
        have hb2eq : S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²) := hxb2
        have hTcard3 : (S.witnessClassAt_v2 s).card = 4 := hTcard2
        have hI2sub3 : S.I2 ⊆ S.witnessClassAt_v2 s := hI2sub
        have hC1eq : S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) :=
          S.selectorShape_v2_lower_forces_v3 (Z := Z.swapI2) hr hs hcard hB hb2 hxb2 hI2sub hp2 hp2C1
        have hC3eq :
            (S.witnessClassAt_v2 s ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
              (S.witnessClassAt_v2 s ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²)) :=
          Or.inl ha3C3
        rcases (p2mCoreSupport S).selectorShape_v3_split Z with ⟨t, ht, hsplit3⟩
        rcases hsplit3 with ⟨hTcard4, hI3sub, hcases3⟩
        rcases hcases3 with hqv1 | hrest
        · exact (p2mBranchSupport S Z).n4d_bB_2_q_eq_v1_impossible hB
            ⟨hB2, hb2eq, hTcard3, hI2sub3, hC1eq, hC3eq⟩
            hqv1
        · rcases hrest with hqa2 | hqb2
          · have hpacket : SelectorV3Qa2Packet S Z t := by
              dsimp [SelectorV3Qa2Packet]
              exact ⟨hI3sub, hqa2⟩
            exact S.n4d_bB_5_q_eq_C_impossible Z hB hB2 hb2eq hI2sub3 hC1eq hC3eq hpacket
          · rcases hqb2 with ⟨p, hp, hpeq, hqeqC2⟩
            exact S.n4d_bB_4_q_eq_E_impossible Z hB hB2 hb2eq hI2sub3 hC1eq hC3eq hqeqC2 hI3sub
      · rcases hqb3 with ⟨p2, hp2, hp2C1, hb3C3⟩
        have hB2 : (Z.b2 : ℝ²) ∈ S.I2 := hb2
        have hb2eq : S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²) := hxb2
        have hTcard3 : (S.witnessClassAt_v2 s).card = 4 := hTcard2
        have hI2sub3 : S.I2 ⊆ S.witnessClassAt_v2 s := hI2sub
        have hC1eq : S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) :=
          S.selectorShape_v2_lower_forces_v3 (Z := Z.swapI2) hr hs hcard hB hb2 hxb2 hI2sub hp2 hp2C1
        have hC3eq :
            (S.witnessClassAt_v2 s ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
              (S.witnessClassAt_v2 s ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²)) :=
          Or.inr hb3C3
        rcases (p2mCoreSupport S).selectorShape_v3_split Z with ⟨t, ht, hsplit3⟩
        rcases hsplit3 with ⟨hTcard4, hI3sub, hcases3⟩
        rcases hcases3 with hqv1 | hrest
        · exact (p2mBranchSupport S Z).n4d_bB_2_q_eq_v1_impossible hB
            ⟨hB2, hb2eq, hTcard3, hI2sub3, hC1eq, hC3eq⟩
            hqv1
        · rcases hrest with hqa2 | hqb2
          · have hpacket : SelectorV3Qa2Packet S Z t := by
              dsimp [SelectorV3Qa2Packet]
              exact ⟨hI3sub, hqa2⟩
            exact S.n4d_bB_5_q_eq_C_impossible Z hB hB2 hb2eq hI2sub3 hC1eq hC3eq hpacket
          · rcases hqb2 with ⟨p, hp, hpeq, hqeqC2⟩
            exact S.n4d_bB_4_q_eq_E_impossible Z hB hB2 hb2eq hI2sub3 hC1eq hC3eq hqeqC2 hI3sub
end Problem97
end Batch3N9
end Batch3N9Unit066
/-- The escaped Form `b` at `v₁` is impossible for a finite endpoint shell. -/
theorem solution {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A) :
    S.N4dExcludesFormB_v1 :=
  Batch3N9.Problem97.FiniteEndpointShell.N4dExcludesFormB_v1_proof S
