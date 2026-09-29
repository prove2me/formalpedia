-- Prove2me | solution 1 for Erdos9796FiniteNine.form_a_v1
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T05:30:23.712256+00:00
-- url     : https://prove2.me/submissions/c8238e1b-ad33-43cc-8566-185a03a405e6

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N4dPackets
import Theorems.Thm_Erdos9796FiniteNine_n4e_core
import Theorems.Thm_Erdos9796FiniteNine_form_b_v2
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

section Batch3N9FormAGeometrySupport
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
end Batch3N9FormAGeometrySupport

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


section Batch3N9FormASupport
namespace Batch3N9
open scoped EuclideanGeometry InnerProductSpace
open Finset
namespace Problem97
namespace FiniteEndpointShell

noncomputable def p2mCoreSupport {A : Finset ℝ²}
    (S : FiniteEndpointShell A) : N4eCoreSupport S :=
  Classical.choice (Erdos9796FiniteNine.n4e_core S)

/-- Reconstruct the unsplit selector shape from the public three-case support field. -/
theorem p2mSelectorShape_v3 {A : Finset ℝ²}
    (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S) :
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
  rcases (p2mCoreSupport S).selectorShape_v3_split Z with ⟨r, hr, hshape⟩
  dsimp at hshape
  rcases hshape with ⟨hTcard, hI3sub, hcase⟩
  refine ⟨r, hr, ?_⟩
  dsimp
  rcases hcase with h | h | h
  · rcases h with ⟨p, hp, hpC1, hv1C2⟩
    exact ⟨hTcard, hI3sub, p, S.triangle.v1, hp, by simp, hpC1, hv1C2⟩
  · rcases h with ⟨p, hp, hpC1, ha2C2⟩
    exact ⟨hTcard, hI3sub, p, Z.a2, hp, by simp, hpC1, ha2C2⟩
  · rcases h with ⟨p, hp, hpC1, hb2C2⟩
    exact ⟨hTcard, hI3sub, p, Z.b2, hp, by simp, hpC1, hb2C2⟩

end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9FormASupport
-- Original module: Solutions.Batch3N9.N4d.FormAEndpointPairKill
section Batch3N9Unit053
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell
theorem b3n9m053_hneg_of_cyclicShift_local'
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
theorem b3n9m053_supportCap_interval_of_oppositeFirst_local'
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
theorem b3n9m053_c1_vertex_same_open_side_as_v2'
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {p : ℝ²}
    (hpI1 : p ∈ S.I1) :
    0 < signedArea2 p S.triangle.v1 S.triangle.v3 *
      signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 := by
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
  have hv3A : S.triangle.v3 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact S.triangle.v3_mem
  have hv2A : S.triangle.v2 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact S.triangle.v2_mem
  rcases Finset.mem_image.mp hv1A with ⟨i1, _, hi1⟩
  rcases Finset.mem_image.mp hv3A with ⟨i2, _, hi2⟩
  rcases Finset.mem_image.mp hv2A with ⟨i3, _, hi3⟩
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
      (b3n9m053_hneg_of_cyclicShift_local' (phi := phi) hneg i1 hij hjk :
        Problem97.signedArea2 (phi (i + i1)) (phi (j + i1)) (phi (k + i1)) < 0)
  have hpsi0 : psi i0 = S.triangle.v1 := by
    simpa [psi, i0, hi1]
  have hshift_i2 : (i2 - i1) + i1 = i2 := by
    simpa [finCycle] using (Equiv.apply_symm_apply (finCycle i1) i2)
  have hshift_i3 : (i3 - i1) + i1 = i3 := by
    simpa [finCycle] using (Equiv.apply_symm_apply (finCycle i1) i3)
  have hi2_ne_i1 : i2 ≠ i1 := by
    intro h
    exact S.triangle.v13_ne (by simpa [hi1, hi2] using congrArg phi h.symm)
  have hi3_ne_i1 : i3 ≠ i1 := by
    intro h
    exact S.triangle.v12_ne (by simpa [hi1, hi3] using congrArg phi h.symm)
  have hi2_ne_i3 : i2 ≠ i3 := by
    intro h
    exact S.triangle.v23_ne.symm (by simpa [hi2, hi3] using congrArg phi h)
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
  · have hpsi_i2 : psi (i2 - i1) = S.triangle.v3 := by
      simpa [psi, hshift_i2] using hi2
    have hpsi_i3 : psi (i3 - i1) = S.triangle.v2 := by
      simpa [psi, hshift_i3] using hi3
    have hC1_interval :
        ∀ x : ℝ², x ∈ S.CP.C1 ↔
          ∃ q : Fin n, i2 - i1 ≤ q ∧ q ≤ i3 - i1 ∧ psi q = x := by
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
      simpa [psi, hshift_i2, hshift_i3] using
        b3n9m053_supportCap_interval_of_oppositeFirst_local'
          (A := A) (C := S.CP.C1) (phi := psi)
          hpsi_inj hpsi_image hneg_shift S.CP.C1_subset
          hC1_arc_swap
          S.CP.v3_mem_C1 S.CP.v2_mem_C1
          (u_idx := i0) (v_idx := i2 - i1) (w_idx := i3 - i1)
          hpsi0 hpsi_i2 hpsi_i3 hi2_pos h23
    rcases (hC1_interval p).1 hpC1 with ⟨q, hqlo, hqhi, hqeq⟩
    have hq_ne_left : q ≠ i2 - i1 := by
      intro hq
      apply hp_ne_v3
      calc
        p = psi q := hqeq.symm
        _ = psi (i2 - i1) := by simp [hq]
        _ = S.triangle.v3 := hpsi_i2
    have hq_ne_right : q ≠ i3 - i1 := by
      intro hq
      apply hp_ne_v2
      calc
        p = psi q := hqeq.symm
        _ = psi (i3 - i1) := by simp [hq]
        _ = S.triangle.v2 := hpsi_i3
    have hqgt : i2 - i1 < q := lt_of_le_of_ne hqlo hq_ne_left.symm
    have hqlt3 : q < i3 - i1 := lt_of_le_of_ne hqhi hq_ne_right
    have hp_neg :
        Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi q) < 0 := hneg_shift hi2_pos hqgt
    have hv2_neg :
        Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi (i3 - i1)) < 0 := hneg_shift hi2_pos h23
    have hp_side : Problem97.signedArea2 p S.triangle.v1 S.triangle.v3 < 0 := by
      rw [← hqeq, ← hpsi0, ← hpsi_i2]
      simpa [hcyc] using hp_neg
    have hv2_side :
        Problem97.signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 < 0 := by
      rw [← hpsi0, ← hpsi_i2, ← hpsi_i3]
      simpa [hcyc] using hv2_neg
    exact mul_pos_of_neg_of_neg hp_side hv2_side
  · have h32 : i3 - i1 < i2 - i1 := by
      have hle : i3 - i1 ≤ i2 - i1 := le_of_not_gt h23
      have hne : i3 - i1 ≠ i2 - i1 := by
        intro h
        apply hi2_ne_i3
        have h' := congrArg (fun t : Fin n => t + i1) h
        simpa [hshift_i2, hshift_i3] using h'.symm
      exact lt_of_le_of_ne hle hne
    have hpsi_i2 : psi (i2 - i1) = S.triangle.v3 := by
      simpa [psi, hshift_i2] using hi2
    have hpsi_i3 : psi (i3 - i1) = S.triangle.v2 := by
      simpa [psi, hshift_i3] using hi3
    have hC1_interval :
        ∀ x : ℝ², x ∈ S.CP.C1 ↔
          ∃ q : Fin n, i3 - i1 ≤ q ∧ q ≤ i2 - i1 ∧ psi q = x := by
      simpa [psi, hshift_i2, hshift_i3] using
        b3n9m053_supportCap_interval_of_oppositeFirst_local'
          (A := A) (C := S.CP.C1) (phi := psi)
          hpsi_inj hpsi_image hneg_shift S.CP.C1_subset
          (fun x hxA => (S.CP.arc_membership x hxA).1) S.CP.v2_mem_C1 S.CP.v3_mem_C1
          (u_idx := i0) (v_idx := i3 - i1) (w_idx := i2 - i1)
          hpsi0 hpsi_i3 hpsi_i2 hi3_pos h32
    rcases (hC1_interval p).1 hpC1 with ⟨q, hqlo, hqhi, hqeq⟩
    have hq_ne_left : q ≠ i3 - i1 := by
      intro hq
      apply hp_ne_v2
      calc
        p = psi q := hqeq.symm
        _ = psi (i3 - i1) := by simp [hq]
        _ = S.triangle.v2 := hpsi_i3
    have hq_ne_right : q ≠ i2 - i1 := by
      intro hq
      apply hp_ne_v3
      calc
        p = psi q := hqeq.symm
        _ = psi (i2 - i1) := by simp [hq]
        _ = S.triangle.v3 := hpsi_i2
    have hqgt : i3 - i1 < q := lt_of_le_of_ne hqlo hq_ne_left.symm
    have hqlt2 : q < i2 - i1 := lt_of_le_of_ne hqhi hq_ne_right
    have hp_mid :
        Problem97.signedArea2 (psi i0) (psi q) (psi (i2 - i1)) < 0 :=
      hneg_shift (lt_trans hi3_pos hqgt) hqlt2
    have hv2_mid :
        Problem97.signedArea2 (psi i0) (psi (i3 - i1)) (psi (i2 - i1)) < 0 :=
      hneg_shift hi3_pos h32
    have hp_side : 0 < Problem97.signedArea2 p S.triangle.v1 S.triangle.v3 := by
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
    have hv2_side : 0 < Problem97.signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 := by
      rw [← hpsi0, ← hpsi_i2, ← hpsi_i3]
      have hv2_side' : 0 < Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi (i3 - i1)) := by
        have hswap_3 :
            Problem97.signedArea2 (psi i0) (psi (i3 - i1)) (psi (i2 - i1)) =
              -Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi (i3 - i1)) := by
          simpa using (hswap (a := psi i0) (b := psi (i3 - i1)) (c := psi (i2 - i1)))
        have : -Problem97.signedArea2 (psi i0) (psi (i2 - i1)) (psi (i3 - i1)) < 0 := by
          rw [← hswap_3]
          exact hv2_mid
        linarith
      simpa [hcyc] using hv2_side'
    exact mul_pos hp_side hv2_side
theorem b3n9m053_c3_sameSide_core' (p q s t c : ℝ)
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
theorem b3n9m053_c3_vertex_same_open_side_as_v2'
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {a₃ : ℝ²}
    (ha2 : a₃ ∈ S.I3) :
    0 < signedArea2 a₃ S.triangle.v1 S.triangle.v3 *
      signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 := by
  classical
  let q1 : ℝ² := S.triangle.v1
  let q2 : ℝ² := S.triangle.v3
  let q3 : ℝ² := S.triangle.v2
  let a : ℝ² := a₃
  let center : ℝ² := S.Packet.center
  have haC2 : a ∈ S.CP.C3 :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp ha2).2).2
  have ha_ne_v1 : a ≠ q1 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha2).2).1
  have ha_ne_v3 : a ≠ q3 := (Finset.mem_erase.mp ha2).1
  have haA : a ∈ A := S.CP.C3_subset haC2
  have harc_le :
      signedArea2 a q3 q1 * signedArea2 q2 q3 q1 ≤ 0 := by
    have hraw : signedArea2 a q1 q3 * signedArea2 q2 q1 q3 ≤ 0 :=
      (S.CP.arc_membership a haA).2.2.1 haC2
    have hswap_a : signedArea2 a q3 q1 = -signedArea2 a q1 q3 := by
      unfold Problem97.signedArea2
      ring
    have hswap_q2 : signedArea2 q2 q3 q1 = -signedArea2 q2 q1 q3 := by
      unfold Problem97.signedArea2
      ring
    rw [hswap_a, hswap_q2]
    simpa using hraw
  have hav3v1_ne : signedArea2 a q3 q1 ≠ 0 := by
    intro hΔ
    have hcol : Collinear ℝ ({a, q3, q1} : Set ℝ²) :=
      Problem97.collinear_of_signedArea2_eq_zero a q3 q1 hΔ
    have hconv : ConvexIndep A := S.hconv
    have h3A : q3 ∈ A := S.triangle.v2_mem
    have h1A : q1 ∈ A := S.triangle.v1_mem
    rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
    · apply hconv q3 (by exact_mod_cast h3A)
      have hseg : q3 ∈ segment ℝ a q1 := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨by exact_mod_cast haA, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha_ne_v3 h⟩
      · rcases hx with rfl
        exact ⟨by exact_mod_cast h1A, by
          simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v12_ne h⟩
    · apply hconv q1 (by exact_mod_cast h1A)
      have hseg : q1 ∈ segment ℝ q3 a := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨by exact_mod_cast h3A, by
          simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v12_ne h.symm⟩
      · rcases hx with rfl
        exact ⟨by exact_mod_cast haA, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha_ne_v1 h⟩
    · apply hconv a (by exact_mod_cast haA)
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
    have hv2O : ‖q2 - S.Packet.center‖ = S.Packet.radius := S.Packet.moser_on_boundary_3
    have hv3O : ‖q3 - S.Packet.center‖ = S.Packet.radius := S.Packet.moser_on_boundary_2
    exact MEC.signedArea2_ne_zero_of_three_dist_eq
      (by simpa [dist_eq_norm] using hv2O)
      (by simpa [dist_eq_norm] using hv3O)
      (by simpa [dist_eq_norm] using hv1O)
      S.triangle.v23_ne.symm S.triangle.v12_ne.symm S.triangle.v13_ne.symm
  have harc : signedArea2 a q3 q1 * signedArea2 q2 q3 q1 < 0 :=
    lt_of_le_of_ne harc_le (mul_ne_zero hav3v1_ne hv2v3v1_ne)
  have hu : q2 - q1 ≠ 0 := sub_ne_zero.mpr S.triangle.v13_ne.symm
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
      exact S.Packet.moser_on_boundary_1.trans S.Packet.moser_on_boundary_3.symm
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
      rw [dist_comm, dist_eq_norm]; exact S.Packet.moser_on_boundary_1
    have := hdist_center_sq q1
    rw [hr, hX_q1, hY_q1] at this
    rw [this]; ring
  have hC1 : 8 * yc * Y q3 = 4 * (X q3) ^ 2 + 4 * (Y q3) ^ 2 - 1 := by
    have hr : dist center q3 = S.Packet.radius := by
      rw [dist_comm, dist_eq_norm]; exact S.Packet.moser_on_boundary_2
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
      simpa [q2, center] using S.Packet.moser_on_boundary_3
    have hq3O : ‖q3 - center‖ = S.Packet.radius := by
      simpa [q3, center] using S.Packet.moser_on_boundary_2
    have hinn : inner ℝ (q1 - q3) (q2 - q3) ≥ 0 := by
      simpa [q1, q2, q3, real_inner_comm] using S.Packet.inner_at_v2
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
    b3n9m053_c3_sameSide_core' (X a) (Y a) (X q3) (Y q3) yc hcenter_q3 hARC hD hC1
  have hsa_a : signedArea2 a q1 q2 = Y a * ‖u‖ ^ 2 := by
    rw [harea_gen a q1 q2, hX_q1, hY_q1, hX_q2, hY_q2]; ring
  have hsa_3 : signedArea2 q3 q1 q2 = Y q3 * ‖u‖ ^ 2 := by
    rw [harea_gen q3 q1 q2, hX_q1, hY_q1, hX_q2, hY_q2]; ring
  change 0 < signedArea2 a q1 q2 * signedArea2 q3 q1 q2
  rw [hsa_a, hsa_3]
  have : Y a * ‖u‖ ^ 2 * (Y q3 * ‖u‖ ^ 2) = (Y a * Y q3) * (‖u‖ ^ 2 * ‖u‖ ^ 2) := by ring
  rw [this]
  exact mul_pos hcore (mul_pos hu_sq_pos hu_sq_pos)
theorem b3n9m053_bisector_separates
    {c x u w : ℝ²} {τ ρ : ℝ}
    (huc : dist u c = τ) (hwc : dist w c = τ)
    (hux : dist u x = ρ) (hwx : dist w x = ρ)
    (hne : u ≠ w)
    (hucol : signedArea2 u c x ≠ 0) :
    signedArea2 u c x * signedArea2 w c x < 0 := by
  have hmid : signedArea2 (midpoint ℝ w u) c x = 0 :=
    twoCircle_midpoint_collinear huc hwc hux hwx hne
  have hrefl : signedArea2 u c x = - signedArea2 w c x :=
    signedArea2_reflection_neg hmid
  have hwne : signedArea2 w c x ≠ 0 := by
    intro h; apply hucol; rw [hrefl, h]; ring
  rw [hrefl]
  nlinarith only [hwne, sq_pos_of_ne_zero hwne]
theorem b3n9m053_sieve_at_most_one_on_xcircle
    {c x : ℝ²} {τ ρ σ : ℝ}
    {P : Finset ℝ²}
    (hcirc : ∀ p ∈ P, dist p c = τ)
    (hside : ∀ p ∈ P, 0 < signedArea2 p c x * σ) :
    (P.filter (fun p => dist p x = ρ)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro u hu w hw
  rcases Finset.mem_filter.mp hu with ⟨huP, hux⟩
  rcases Finset.mem_filter.mp hw with ⟨hwP, hwx⟩
  by_contra hne
  have huc : dist u c = τ := hcirc u huP
  have hwc : dist w c = τ := hcirc w hwP
  have husgn : 0 < signedArea2 u c x * σ := hside u huP
  have hwsgn : 0 < signedArea2 w c x * σ := hside w hwP
  have hucol : signedArea2 u c x ≠ 0 := by
    intro h; rw [h, zero_mul] at husgn; exact lt_irrefl 0 husgn
  have hsep : signedArea2 u c x * signedArea2 w c x < 0 :=
    b3n9m053_bisector_separates huc hwc hux hwx hne hucol
  nlinarith only [husgn, hwsgn, hsep, mul_pos husgn hwsgn, sq_nonneg σ]
theorem b3n9m053_boundaryOrder_hneg
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    ∃ (n : ℕ) (phi : Fin n → ℝ²),
      Function.Injective phi ∧ Finset.univ.image phi = A ∧
      (∀ {i j k : Fin n}, i < j → j < k →
        Problem97.signedArea2 (phi i) (phi j) (phi k) < 0) ∧ 0 < n := by
  classical
  obtain ⟨n, hn, phi, hphi_inj, hphi_image, hccw⟩ :=
    Problem97.CGN.CGN4g0_globalBoundaryOrder_of_convexIndep S.hconv S.hnoncol
  refine ⟨n, phi, hphi_inj, hphi_image, ?_, by omega⟩
  intro i j k hij hjk
  have hij_ne : phi i ≠ phi j := fun h => (ne_of_lt hij) (hphi_inj h)
  have hkj_ne : phi k ≠ phi j := fun h => (ne_of_gt hjk) (hphi_inj h)
  have hsign : SignType.sign (Problem97.signedArea2 (phi j) (phi i) (phi k)) = 1 := by
    rw [Problem97.signedArea2_sign_eq_oangle_sign (phi j) (phi i) (phi k) hij_ne hkj_ne]
    exact hccw.sign_oangle hij hjk
  have hpos : 0 < Problem97.signedArea2 (phi j) (phi i) (phi k) := (sign_eq_one_iff).mp hsign
  have hswap : Problem97.signedArea2 (phi j) (phi i) (phi k) =
      -Problem97.signedArea2 (phi i) (phi j) (phi k) := by simp [Problem97.signedArea2]; ring
  linarith
theorem b3n9m053_shift_boundaryOrder
    {A : Finset ℝ²} {n : ℕ} [NeZero n] {phi : Fin n → ℝ²}
    (hphi_inj : Function.Injective phi) (hphi_image : Finset.univ.image phi = A)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (ic : Fin n) :
    ∃ psi : Fin n → ℝ², Function.Injective psi ∧ Finset.univ.image psi = A ∧
      (∀ {i j k : Fin n}, i < j → j < k →
        Problem97.signedArea2 (psi i) (psi j) (psi k) < 0) ∧
      (∀ i : Fin n, psi (i - ic) = phi i) := by
  classical
  refine ⟨fun t => phi (t + ic), ?_, ?_, ?_, ?_⟩
  · intro a b hab; apply (finCycle ic).injective; exact hphi_inj hab
  · ext y
    constructor
    · intro hy; rcases Finset.mem_image.mp hy with ⟨t, _, rfl⟩
      rw [← hphi_image]; exact Finset.mem_image_of_mem phi (Finset.mem_univ _)
    · intro hy; rw [← hphi_image] at hy
      rcases Finset.mem_image.mp hy with ⟨q, _, rfl⟩
      refine Finset.mem_image.mpr ⟨q - ic, Finset.mem_univ _, ?_⟩; simp
  · intro i j k hij hjk; exact b3n9m053_hneg_of_cyclicShift_local' (phi := phi) hneg ic hij hjk
  · intro i; simp
theorem b3n9m053_sa_neg_abc {n : ℕ} {psi : Fin n → ℝ²}
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (psi i) (psi j) (psi k) < 0)
    {a b c : Fin n} (h1 : a < b) (h2 : b < c) :
    Problem97.signedArea2 (psi a) (psi b) (psi c) < 0 := hneg h1 h2
theorem b3n9m053_sa_neg_bca {n : ℕ} {psi : Fin n → ℝ²}
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (psi i) (psi j) (psi k) < 0)
    {a b c : Fin n} (h1 : b < c) (h2 : c < a) :
    Problem97.signedArea2 (psi a) (psi b) (psi c) < 0 := by
  have hcyc {p q r : ℝ²} :
      Problem97.signedArea2 p q r = Problem97.signedArea2 r p q := by
    simp only [Problem97.signedArea2]; ring
  rw [hcyc, hcyc]; exact hneg h1 h2
theorem b3n9m053_sa_pos_acb {n : ℕ} {psi : Fin n → ℝ²}
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (psi i) (psi j) (psi k) < 0)
    {a b c : Fin n} (h1 : a < c) (h2 : c < b) :
    0 < Problem97.signedArea2 (psi a) (psi b) (psi c) := by
  have hswap {p q r : ℝ²} :
      Problem97.signedArea2 p q r = - Problem97.signedArea2 p r q := by
    simp only [Problem97.signedArea2]; ring
  have h := hneg h1 h2; rw [hswap]; linarith
theorem b3n9m053_sa_pos_between {n : ℕ} {psi : Fin n → ℝ²}
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (psi i) (psi j) (psi k) < 0)
    {iq ipt ir : Fin n} (h1 : iq < ipt) (h2 : ipt < ir) :
    0 < Problem97.signedArea2 (psi ipt) (psi iq) (psi ir) := by
  have hcyc {p q r : ℝ²} :
      Problem97.signedArea2 p q r = Problem97.signedArea2 r p q := by
    simp only [Problem97.signedArea2]; ring
  rw [hcyc, hcyc]; exact b3n9m053_sa_pos_acb hneg h1 h2
theorem b3n9m053_index_between_of_onArc {n : ℕ} {psi : Fin n → ℝ²}
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (psi i) (psi j) (psi k) < 0)
    {ip iq ir ipt : Fin n} (hqr : iq < ir) (hp : ip < iq ∨ ir < ip)
    (hne_q : ipt ≠ iq) (hne_r : ipt ≠ ir)
    (harc : Problem97.OnArcOpposite (psi ip) (psi iq) (psi ir) (psi ipt)) :
    iq < ipt ∧ ipt < ir := by
  unfold Problem97.OnArcOpposite at harc
  have hp_neg : Problem97.signedArea2 (psi ip) (psi iq) (psi ir) < 0 := by
    rcases hp with h | h
    · exact b3n9m053_sa_neg_abc hneg h hqr
    · exact b3n9m053_sa_neg_bca hneg hqr h
  have hpt_nonneg : 0 ≤ Problem97.signedArea2 (psi ipt) (psi iq) (psi ir) := by
    nlinarith only [harc, hp_neg]
  rcases lt_trichotomy ipt iq with h | h | h
  · exfalso
    have : Problem97.signedArea2 (psi ipt) (psi iq) (psi ir) < 0 := b3n9m053_sa_neg_abc hneg h hqr
    linarith
  · exact absurd h hne_q
  · rcases lt_trichotomy ipt ir with h2 | h2 | h2
    · exact ⟨h, h2⟩
    · exact absurd h2 hne_r
    · exfalso
      have : Problem97.signedArea2 (psi ipt) (psi iq) (psi ir) < 0 := b3n9m053_sa_neg_bca hneg hqr h2
      linarith
theorem b3n9m053_index_outside_of_onArc {n : ℕ} {psi : Fin n → ℝ²}
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (psi i) (psi j) (psi k) < 0)
    {ip iq ir ipt : Fin n} (hp1 : iq < ip) (hp2 : ip < ir)
    (hne_q : ipt ≠ iq) (hne_r : ipt ≠ ir)
    (harc : Problem97.OnArcOpposite (psi ip) (psi iq) (psi ir) (psi ipt)) :
    ipt < iq ∨ ir < ipt := by
  unfold Problem97.OnArcOpposite at harc
  have hp_pos : 0 < Problem97.signedArea2 (psi ip) (psi iq) (psi ir) :=
    b3n9m053_sa_pos_between hneg hp1 hp2
  have hpt_nonpos : Problem97.signedArea2 (psi ipt) (psi iq) (psi ir) ≤ 0 := by
    nlinarith only [harc, hp_pos]
  rcases lt_trichotomy ipt iq with h | h | h
  · exact Or.inl h
  · exact absurd h hne_q
  · rcases lt_trichotomy ipt ir with h2 | h2 | h2
    · exfalso
      have : 0 < Problem97.signedArea2 (psi ipt) (psi iq) (psi ir) := b3n9m053_sa_pos_between hneg h h2
      linarith
    · exact absurd h2 hne_r
    · exact Or.inr h2
theorem b3n9m053_onArc_swap_psi {n : ℕ} {psi : Fin n → ℝ²} {ip iq ir ipt : Fin n}
    (h : Problem97.OnArcOpposite (psi ip) (psi iq) (psi ir) (psi ipt)) :
    Problem97.OnArcOpposite (psi ip) (psi ir) (psi iq) (psi ipt) := by
  unfold Problem97.OnArcOpposite at h ⊢
  have e1 : signedArea2 (psi ipt) (psi ir) (psi iq) =
      - signedArea2 (psi ipt) (psi iq) (psi ir) := by simp only [Problem97.signedArea2]; ring
  have e2 : signedArea2 (psi ip) (psi ir) (psi iq) =
      - signedArea2 (psi ip) (psi iq) (psi ir) := by simp only [Problem97.signedArea2]; ring
  rw [e1, e2]; nlinarith only [h]
theorem b3n9m053_c2_arc_swap {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    ∀ z ∈ A, z ∈ S.CP.C2 ↔
      Problem97.OnArcOpposite S.triangle.v2 S.triangle.v1 S.triangle.v3 z := by
  intro z hzA
  rw [(S.CP.arc_membership z hzA).2.1]
  unfold Problem97.OnArcOpposite
  constructor
  · intro hx
    have e1 : signedArea2 z S.triangle.v1 S.triangle.v3 =
        - signedArea2 z S.triangle.v3 S.triangle.v1 := by
      simp only [Problem97.signedArea2]; ring
    have e2 : signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 =
        - signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 := by
      simp only [Problem97.signedArea2]; ring
    rw [e1, e2]; nlinarith only [hx]
  · intro hx
    have e1 : signedArea2 z S.triangle.v3 S.triangle.v1 =
        - signedArea2 z S.triangle.v1 S.triangle.v3 := by
      simp only [Problem97.signedArea2]; ring
    have e2 : signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 =
        - signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 := by
      simp only [Problem97.signedArea2]; ring
    rw [e1, e2]; nlinarith only [hx]
theorem b3n9m053_same_side_of_chord_endpoint_thales
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {x : ℝ²} {t : ℝ}
    (hxI2 : x ∈ S.I2)
    (hv2v3 : dist S.triangle.v2 S.triangle.v3 = t)
    (hv2x : dist S.triangle.v2 x = t) :
    0 < signedArea2 S.triangle.v2 S.triangle.v3 x *
        signedArea2 S.triangle.v1 S.triangle.v3 x := by
  classical
  have hxC2 : x ∈ S.CP.C2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).2
  have hx_ne_v3 : x ≠ S.triangle.v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1
  have hx_ne_v1 : x ≠ S.triangle.v1 := (Finset.mem_erase.mp hxI2).1
  obtain ⟨n, phi, hphi_inj, hphi_image, hneg, hnpos⟩ := b3n9m053_boundaryOrder_hneg S
  haveI : NeZero n := ⟨by omega⟩
  have hv1A : S.triangle.v1 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v1_mem
  have hv2A : S.triangle.v2 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v2_mem
  have hv3A : S.triangle.v3 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v3_mem
  rcases Finset.mem_image.mp hv1A with ⟨i1, _, hi1⟩
  rcases Finset.mem_image.mp hv2A with ⟨i2, _, hi2⟩
  rcases Finset.mem_image.mp hv3A with ⟨i3, _, hi3⟩
  obtain ⟨psi, hpsi_inj, hpsi_image, hneg_s, hpsi_re⟩ :=
    b3n9m053_shift_boundaryOrder hphi_inj hphi_image hneg i2
  set jv2 : Fin n := i2 - i2 with hjv2def
  set jv3 : Fin n := i3 - i2 with hjv3def
  set jv1 : Fin n := i1 - i2 with hjv1def
  have hpv2 : psi jv2 = S.triangle.v2 := by rw [hjv2def, hpsi_re, hi2]
  have hpv3 : psi jv3 = S.triangle.v3 := by rw [hjv3def, hpsi_re, hi3]
  have hpv1 : psi jv1 = S.triangle.v1 := by rw [hjv1def, hpsi_re, hi1]
  have hjv2_zero : jv2 = 0 := by rw [hjv2def]; exact sub_self i2
  have hv3_ne_v2 : jv3 ≠ jv2 := fun h => S.triangle.v23_ne.symm (by rw [← hpv3, ← hpv2, h])
  have hv1_ne_v2 : jv1 ≠ jv2 := fun h => S.triangle.v12_ne (by rw [← hpv1, ← hpv2, h])
  have hv1_ne_v3 : jv1 ≠ jv3 := fun h => S.triangle.v13_ne (by rw [← hpv1, ← hpv3, h])
  have h0_lt_jv3 : jv2 < jv3 :=
    hjv2_zero ▸ Fin.pos_iff_ne_zero.mpr (fun h => hv3_ne_v2 (hjv2_zero ▸ h))
  have h0_lt_jv1 : jv2 < jv1 :=
    hjv2_zero ▸ Fin.pos_iff_ne_zero.mpr (fun h => hv1_ne_v2 (hjv2_zero ▸ h))
  have hxA : x ∈ A := S.CP.C2_subset hxC2
  by_cases h31 : jv3 < jv1
  ·
    have hC2int := b3n9m053_supportCap_interval_of_oppositeFirst_local'
      (A := A) (C := S.CP.C2) (phi := psi) (u := S.triangle.v2) (v := S.triangle.v3)
        (w := S.triangle.v1)
      hpsi_inj hpsi_image hneg_s S.CP.C2_subset
      (fun z hzA => (S.CP.arc_membership z hzA).2.1)
      S.CP.v3_mem_C2 S.CP.v1_mem_C2 hpv2 hpv3 hpv1 h0_lt_jv3 h31
    rcases (hC2int x).1 hxC2 with ⟨ix, hlo, hhi, hxq⟩
    have hix_ne_lo : ix ≠ jv3 := fun h => hx_ne_v3 (by rw [← hxq, h, hpv3])
    have hix_ne_hi : ix ≠ jv1 := fun h => hx_ne_v1 (by rw [← hxq, h, hpv1])
    have h3x : jv3 < ix := lt_of_le_of_ne hlo (Ne.symm hix_ne_lo)
    have hx1 : ix < jv1 := lt_of_le_of_ne hhi hix_ne_hi
    have hv1_side : signedArea2 S.triangle.v1 S.triangle.v3 x < 0 := by
      rw [← hpv1, ← hpv3, ← hxq]; exact b3n9m053_sa_neg_bca hneg_s h3x hx1
    have hv2_side : signedArea2 S.triangle.v2 S.triangle.v3 x < 0 := by
      rw [← hpv2, ← hpv3, ← hxq]; exact b3n9m053_sa_neg_abc hneg_s h0_lt_jv3 h3x
    exact mul_pos_of_neg_of_neg hv2_side hv1_side
  ·
    have h13 : jv1 < jv3 := lt_of_le_of_ne (le_of_not_gt h31) hv1_ne_v3
    have hC2int := b3n9m053_supportCap_interval_of_oppositeFirst_local'
      (A := A) (C := S.CP.C2) (phi := psi) (u := S.triangle.v2) (v := S.triangle.v1)
        (w := S.triangle.v3)
      hpsi_inj hpsi_image hneg_s S.CP.C2_subset
      (b3n9m053_c2_arc_swap S) S.CP.v1_mem_C2 S.CP.v3_mem_C2
      hpv2 hpv1 hpv3 h0_lt_jv1 h13
    rcases (hC2int x).1 hxC2 with ⟨ix, hlo, hhi, hxq⟩
    have hix_ne_lo : ix ≠ jv1 := fun h => hx_ne_v1 (by rw [← hxq, h, hpv1])
    have hix_ne_hi : ix ≠ jv3 := fun h => hx_ne_v3 (by rw [← hxq, h, hpv3])
    have h1x : jv1 < ix := lt_of_le_of_ne hlo (Ne.symm hix_ne_lo)
    have hx3 : ix < jv3 := lt_of_le_of_ne hhi hix_ne_hi
    have hv1_side : 0 < signedArea2 S.triangle.v1 S.triangle.v3 x := by
      rw [← hpv1, ← hpv3, ← hxq]; exact b3n9m053_sa_pos_acb hneg_s h1x hx3
    have hv2_side : 0 < signedArea2 S.triangle.v2 S.triangle.v3 x := by
      rw [← hpv2, ← hpv3, ← hxq]
      exact b3n9m053_sa_pos_acb hneg_s (lt_trans h0_lt_jv1 h1x) hx3
    exact mul_pos hv2_side hv1_side
theorem b3n9m053_c1_same_side_of_v1x_chord
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {a₁ x : ℝ²}
    (ha1I1 : a₁ ∈ S.I1)
    (hxI2 : x ∈ S.I2) :
    0 < signedArea2 a₁ S.triangle.v1 x *
        signedArea2 S.triangle.v3 S.triangle.v1 x := by
  classical
  have hxC2 : x ∈ S.CP.C2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).2
  have hx_ne_v3 : x ≠ S.triangle.v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1
  have hx_ne_v1 : x ≠ S.triangle.v1 := (Finset.mem_erase.mp hxI2).1
  have ha1C1 : a₁ ∈ S.CP.C1 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha1I1).2).2
  have ha1_ne_v3 : a₁ ≠ S.triangle.v3 := (Finset.mem_erase.mp ha1I1).1
  have ha1_ne_v2 : a₁ ≠ S.triangle.v2 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha1I1).2).1
  obtain ⟨n, phi, hphi_inj, hphi_image, hneg, hnpos⟩ := b3n9m053_boundaryOrder_hneg S
  haveI : NeZero n := ⟨by omega⟩
  have hv1A : S.triangle.v1 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v1_mem
  have hv2A : S.triangle.v2 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v2_mem
  have hv3A : S.triangle.v3 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v3_mem
  rcases Finset.mem_image.mp hv1A with ⟨i1, _, hi1⟩
  rcases Finset.mem_image.mp hv2A with ⟨i2, _, hi2⟩
  rcases Finset.mem_image.mp hv3A with ⟨i3, _, hi3⟩
  obtain ⟨psi, hpsi_inj, hpsi_image, hneg_s, hpsi_re⟩ :=
    b3n9m053_shift_boundaryOrder hphi_inj hphi_image hneg i2
  set jv2 : Fin n := i2 - i2 with hjv2def
  set jv3 : Fin n := i3 - i2 with hjv3def
  set jv1 : Fin n := i1 - i2 with hjv1def
  have hpv2 : psi jv2 = S.triangle.v2 := by rw [hjv2def, hpsi_re, hi2]
  have hpv3 : psi jv3 = S.triangle.v3 := by rw [hjv3def, hpsi_re, hi3]
  have hpv1 : psi jv1 = S.triangle.v1 := by rw [hjv1def, hpsi_re, hi1]
  have hjv2_zero : jv2 = 0 := by rw [hjv2def]; exact sub_self i2
  have hv3_ne_v2 : jv3 ≠ jv2 := fun h => S.triangle.v23_ne.symm (by rw [← hpv3, ← hpv2, h])
  have hv1_ne_v2 : jv1 ≠ jv2 := fun h => S.triangle.v12_ne (by rw [← hpv1, ← hpv2, h])
  have hv1_ne_v3 : jv1 ≠ jv3 := fun h => S.triangle.v13_ne (by rw [← hpv1, ← hpv3, h])
  have h0_lt_jv3 : jv2 < jv3 :=
    hjv2_zero ▸ Fin.pos_iff_ne_zero.mpr (fun h => hv3_ne_v2 (hjv2_zero ▸ h))
  have h0_lt_jv1 : jv2 < jv1 :=
    hjv2_zero ▸ Fin.pos_iff_ne_zero.mpr (fun h => hv1_ne_v2 (hjv2_zero ▸ h))
  have ha1A : a₁ ∈ A := S.CP.C1_subset ha1C1
  have ha1arc : Problem97.OnArcOpposite S.triangle.v1 S.triangle.v2 S.triangle.v3 a₁ :=
    (S.CP.arc_membership a₁ ha1A).1.mp ha1C1
  have ha1img : a₁ ∈ Finset.univ.image psi := by rw [hpsi_image]; exact ha1A
  rcases Finset.mem_image.mp ha1img with ⟨ja1, _, hja1⟩
  have ha1_ne_idx_v3 : ja1 ≠ jv3 := fun h => ha1_ne_v3 (by rw [← hja1, h, hpv3])
  have ha1_ne_idx_v2 : ja1 ≠ jv2 := fun h => ha1_ne_v2 (by rw [← hja1, h, hpv2])
  have ha1arc' : Problem97.OnArcOpposite (psi jv1) (psi jv2) (psi jv3) (psi ja1) := by
    rw [hpv1, hpv2, hpv3, hja1]; exact ha1arc
  have hxA : x ∈ A := S.CP.C2_subset hxC2
  have hximg : x ∈ Finset.univ.image psi := by rw [hpsi_image]; exact hxA
  rcases Finset.mem_image.mp hximg with ⟨ix, _, hix⟩
  have hx_ne_idx_v3 : ix ≠ jv3 := fun h => hx_ne_v3 (by rw [← hix, h, hpv3])
  have hx_ne_idx_v1 : ix ≠ jv1 := fun h => hx_ne_v1 (by rw [← hix, h, hpv1])
  have hxarc : Problem97.OnArcOpposite S.triangle.v2 S.triangle.v3 S.triangle.v1 x :=
    (S.CP.arc_membership x hxA).2.1.mp hxC2
  have hxarc' : Problem97.OnArcOpposite (psi jv2) (psi jv3) (psi jv1) (psi ix) := by
    rw [hpv2, hpv3, hpv1, hix]; exact hxarc
  by_cases h31 : jv3 < jv1
  ·
    obtain ⟨h3x, hx1⟩ := b3n9m053_index_between_of_onArc hneg_s (ip := jv2) (iq := jv3) (ir := jv1)
      h31 (Or.inl h0_lt_jv3) hx_ne_idx_v3 hx_ne_idx_v1 hxarc'
    obtain ⟨ha1lo, ha1hi⟩ := b3n9m053_index_between_of_onArc hneg_s (ip := jv1) (iq := jv2) (ir := jv3)
      h0_lt_jv3 (Or.inr h31) ha1_ne_idx_v2 ha1_ne_idx_v3 ha1arc'
    have hv3_side : 0 < signedArea2 S.triangle.v3 S.triangle.v1 x := by
      rw [← hpv3, ← hpv1, ← hix]; exact b3n9m053_sa_pos_acb hneg_s h3x hx1
    have ha1_side : 0 < signedArea2 a₁ S.triangle.v1 x := by
      rw [← hja1, ← hpv1, ← hix]; exact b3n9m053_sa_pos_acb hneg_s (lt_trans ha1hi h3x) hx1
    exact mul_pos ha1_side hv3_side
  ·
    have h13 : jv1 < jv3 := lt_of_le_of_ne (le_of_not_gt h31) hv1_ne_v3
    obtain ⟨h1x, hx3⟩ := b3n9m053_index_between_of_onArc hneg_s (ip := jv2) (iq := jv1) (ir := jv3)
      h13 (Or.inl h0_lt_jv1) hx_ne_idx_v1 hx_ne_idx_v3 (b3n9m053_onArc_swap_psi hxarc')
    have ha1out := b3n9m053_index_outside_of_onArc hneg_s (ip := jv1) (iq := jv2) (ir := jv3)
      h0_lt_jv1 h13 ha1_ne_idx_v2 ha1_ne_idx_v3 ha1arc'
    have hja1_gt : jv3 < ja1 := by
      rcases ha1out with h | h
      · exact absurd h (by rw [hjv2_zero]; exact Fin.not_lt_zero _)
      · exact h
    have hv3_side : signedArea2 S.triangle.v3 S.triangle.v1 x < 0 := by
      rw [← hpv3, ← hpv1, ← hix]; exact b3n9m053_sa_neg_bca hneg_s h1x hx3
    have ha1_side : signedArea2 a₁ S.triangle.v1 x < 0 := by
      rw [← hja1, ← hpv1, ← hix]; exact b3n9m053_sa_neg_bca hneg_s h1x (lt_trans hx3 hja1_gt)
    exact mul_pos_of_neg_of_neg ha1_side hv3_side
theorem b3n9m053_same_side_of_chord_capPair
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {a₃ x : ℝ²}
    (ha3I3 : a₃ ∈ S.I3)
    (hxI2 : x ∈ S.I2) :
    0 < signedArea2 a₃ S.triangle.v3 x *
        signedArea2 S.triangle.v1 S.triangle.v3 x := by
  classical
  have hxC2 : x ∈ S.CP.C2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).2
  have hx_ne_v3 : x ≠ S.triangle.v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1
  have hx_ne_v1 : x ≠ S.triangle.v1 := (Finset.mem_erase.mp hxI2).1
  have ha3C3 : a₃ ∈ S.CP.C3 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha3I3).2).2
  have ha3_ne_v2 : a₃ ≠ S.triangle.v2 := (Finset.mem_erase.mp ha3I3).1
  have ha3_ne_v1 : a₃ ≠ S.triangle.v1 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha3I3).2).1
  obtain ⟨n, phi, hphi_inj, hphi_image, hneg, hnpos⟩ := b3n9m053_boundaryOrder_hneg S
  haveI : NeZero n := ⟨by omega⟩
  have hv1A : S.triangle.v1 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v1_mem
  have hv2A : S.triangle.v2 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v2_mem
  have hv3A : S.triangle.v3 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v3_mem
  rcases Finset.mem_image.mp hv1A with ⟨i1, _, hi1⟩
  rcases Finset.mem_image.mp hv2A with ⟨i2, _, hi2⟩
  rcases Finset.mem_image.mp hv3A with ⟨i3, _, hi3⟩
  obtain ⟨psi, hpsi_inj, hpsi_image, hneg_s, hpsi_re⟩ :=
    b3n9m053_shift_boundaryOrder hphi_inj hphi_image hneg i2
  set jv2 : Fin n := i2 - i2 with hjv2def
  set jv3 : Fin n := i3 - i2 with hjv3def
  set jv1 : Fin n := i1 - i2 with hjv1def
  have hpv2 : psi jv2 = S.triangle.v2 := by rw [hjv2def, hpsi_re, hi2]
  have hpv3 : psi jv3 = S.triangle.v3 := by rw [hjv3def, hpsi_re, hi3]
  have hpv1 : psi jv1 = S.triangle.v1 := by rw [hjv1def, hpsi_re, hi1]
  have hjv2_zero : jv2 = 0 := by rw [hjv2def]; exact sub_self i2
  have hv3_ne_v2 : jv3 ≠ jv2 := fun h => S.triangle.v23_ne.symm (by rw [← hpv3, ← hpv2, h])
  have hv1_ne_v2 : jv1 ≠ jv2 := fun h => S.triangle.v12_ne (by rw [← hpv1, ← hpv2, h])
  have hv1_ne_v3 : jv1 ≠ jv3 := fun h => S.triangle.v13_ne (by rw [← hpv1, ← hpv3, h])
  have h0_lt_jv3 : jv2 < jv3 :=
    hjv2_zero ▸ Fin.pos_iff_ne_zero.mpr (fun h => hv3_ne_v2 (hjv2_zero ▸ h))
  have h0_lt_jv1 : jv2 < jv1 :=
    hjv2_zero ▸ Fin.pos_iff_ne_zero.mpr (fun h => hv1_ne_v2 (hjv2_zero ▸ h))
  have ha3A : a₃ ∈ A := S.CP.C3_subset ha3C3
  have ha3arc : Problem97.OnArcOpposite S.triangle.v3 S.triangle.v1 S.triangle.v2 a₃ :=
    (S.CP.arc_membership a₃ ha3A).2.2.mp ha3C3
  have ha3img : a₃ ∈ Finset.univ.image psi := by rw [hpsi_image]; exact ha3A
  rcases Finset.mem_image.mp ha3img with ⟨ja3, _, hja3⟩
  have ha3_ne_idx_v1 : ja3 ≠ jv1 := fun h => ha3_ne_v1 (by rw [← hja3, h, hpv1])
  have ha3_ne_idx_v2 : ja3 ≠ jv2 := fun h => ha3_ne_v2 (by rw [← hja3, h, hpv2])
  have ha3arc' : Problem97.OnArcOpposite (psi jv3) (psi jv1) (psi jv2) (psi ja3) := by
    rw [hpv3, hpv1, hpv2, hja3]; exact ha3arc
  have ha3arc_sw : Problem97.OnArcOpposite (psi jv3) (psi jv2) (psi jv1) (psi ja3) :=
    b3n9m053_onArc_swap_psi ha3arc'
  have hxA : x ∈ A := S.CP.C2_subset hxC2
  have hximg : x ∈ Finset.univ.image psi := by rw [hpsi_image]; exact hxA
  rcases Finset.mem_image.mp hximg with ⟨ix, _, hix⟩
  have hx_ne_idx_v3 : ix ≠ jv3 := fun h => hx_ne_v3 (by rw [← hix, h, hpv3])
  have hx_ne_idx_v1 : ix ≠ jv1 := fun h => hx_ne_v1 (by rw [← hix, h, hpv1])
  have hxarc : Problem97.OnArcOpposite S.triangle.v2 S.triangle.v3 S.triangle.v1 x :=
    (S.CP.arc_membership x hxA).2.1.mp hxC2
  have hxarc' : Problem97.OnArcOpposite (psi jv2) (psi jv3) (psi jv1) (psi ix) := by
    rw [hpv2, hpv3, hpv1, hix]; exact hxarc
  by_cases h31 : jv3 < jv1
  ·
    obtain ⟨h3x, hx1⟩ := b3n9m053_index_between_of_onArc hneg_s (ip := jv2) (iq := jv3) (ir := jv1)
      h31 (Or.inl h0_lt_jv3) hx_ne_idx_v3 hx_ne_idx_v1 hxarc'
    have ha3out := b3n9m053_index_outside_of_onArc hneg_s (ip := jv3) (iq := jv2) (ir := jv1)
      h0_lt_jv3 h31 ha3_ne_idx_v2 ha3_ne_idx_v1 ha3arc_sw
    have hja3_gt : jv1 < ja3 := by
      rcases ha3out with h | h
      · exact absurd h (by rw [hjv2_zero]; exact Fin.not_lt_zero _)
      · exact h
    have hv1_side : signedArea2 S.triangle.v1 S.triangle.v3 x < 0 := by
      rw [← hpv1, ← hpv3, ← hix]; exact b3n9m053_sa_neg_bca hneg_s h3x hx1
    have ha3_side : signedArea2 a₃ S.triangle.v3 x < 0 := by
      rw [← hja3, ← hpv3, ← hix]; exact b3n9m053_sa_neg_bca hneg_s h3x (lt_trans hx1 hja3_gt)
    exact mul_pos_of_neg_of_neg ha3_side hv1_side
  ·
    have h13 : jv1 < jv3 := lt_of_le_of_ne (le_of_not_gt h31) hv1_ne_v3
    obtain ⟨h1x, hx3⟩ := b3n9m053_index_between_of_onArc hneg_s (ip := jv2) (iq := jv1) (ir := jv3)
      h13 (Or.inl h0_lt_jv1) hx_ne_idx_v1 hx_ne_idx_v3 (b3n9m053_onArc_swap_psi hxarc')
    obtain ⟨ha0, ha1⟩ := b3n9m053_index_between_of_onArc hneg_s (ip := jv3) (iq := jv2) (ir := jv1)
      h0_lt_jv1 (Or.inr h13) ha3_ne_idx_v2 ha3_ne_idx_v1 ha3arc_sw
    have hv1_side : 0 < signedArea2 S.triangle.v1 S.triangle.v3 x := by
      rw [← hpv1, ← hpv3, ← hix]; exact b3n9m053_sa_pos_acb hneg_s h1x hx3
    have ha3_side : 0 < signedArea2 a₃ S.triangle.v3 x := by
      rw [← hja3, ← hpv3, ← hix]; exact b3n9m053_sa_pos_acb hneg_s (lt_trans ha1 h1x) hx3
    exact mul_pos ha3_side hv1_side
set_option maxHeartbeats 4000000 in
theorem b3n9m053_c3_same_side_of_v3x_chord
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {a₃ x : ℝ²} {t : ℝ}
    (ha3I3 : a₃ ∈ S.I3)
    (hxI2 : x ∈ S.I2)
    (hv2v3 : dist S.triangle.v2 S.triangle.v3 = t)
    (hv2x : dist S.triangle.v2 x = t)
    (ht : 0 < t) :
    0 < signedArea2 a₃ S.triangle.v3 x *
        signedArea2 S.triangle.v2 S.triangle.v3 x := by
  classical
  have hne23 : S.triangle.v3 ≠ x := by
    have hx_ne_v3 : x ≠ S.MT.toMoserTriangle.v3 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1
    exact fun h => hx_ne_v3 h.symm
  set q1 : ℝ² := S.triangle.v3 with hq1
  set q2 : ℝ² := x with hq2
  set p2 : ℝ² := S.triangle.v2 with hp2
  have hu : q2 - q1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne23)
  set u : ℝ² := q2 - q1 with hudef
  set nvec : ℝ² := Problem97.stdOrientation.rightAngleRotation u with hnvecdef
  set β := Problem97.stdOrientation.basisRightAngleRotation u hu with hβdef
  set M : ℝ² := midpoint ℝ q1 q2 with hMdef
  set X : ℝ² → ℝ := fun z => β.repr (z - M) 0 with hXdef
  set Y : ℝ² → ℝ := fun z => β.repr (z - M) 1 with hYdef
  have hsum_pt : ∀ z : ℝ², z - M = X z • u + Y z • nvec := by
    intro z
    simpa [hβdef, hXdef, hYdef, hnvecdef] using (β.sum_repr (z - M)).symm
  have horth : inner ℝ u nvec = 0 := by
    simpa [hnvecdef] using Problem97.stdOrientation.inner_rightAngleRotation_self u
  have hu_sq_pos : 0 < ‖u‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
  have hdiff : ∀ z w : ℝ², z - w = (X z - X w) • u + (Y z - Y w) • nvec := by
    intro z w
    have h : (z - M) - (w - M) = z - w := by abel
    rw [← h, hsum_pt z, hsum_pt w, sub_smul, sub_smul]; abel
  have harea_u_left : ∀ r : ℝ, Problem97.stdOrientation.areaForm u (r • u) = 0 := by
    intro r; rw [map_smul]; simp
  have harea_u_right : ∀ r : ℝ,
      Problem97.stdOrientation.areaForm u (r • nvec) = r * ‖u‖ ^ 2 := by
    intro r; rw [map_smul]
    simp [hnvecdef, Orientation.areaForm_rightAngleRotation_right]
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
  have harea_gen : ∀ z w v : ℝ²,
      signedArea2 z w v =
        ((X w - X z) * (Y v - Y z) - (Y w - Y z) * (X v - X z)) * ‖u‖ ^ 2 := by
    intro z w v
    rw [Problem97.signedArea2_eq_stdOrientation_areaForm, hdiff w z, hdiff v z,
        harea_bilin]
  have hq1mid : q1 - M = (-(1 / 2 : ℝ)) • u := by
    calc
      q1 - M = (1 / 2 : ℝ) • (q1 - q2) := by
        simpa [hMdef] using (left_sub_midpoint ℝ q1 q2)
      _ = (-(1 / 2 : ℝ)) • u := by
        rw [show q1 - q2 = -u by rw [hudef]; abel]; simp [smul_neg]
  have hq2mid : q2 - M = (1 / 2 : ℝ) • u := by
    simpa [hMdef, hudef] using (right_sub_midpoint ℝ q1 q2)
  have hβu : β.repr u = Finsupp.single 0 (1 : ℝ) := by
    simpa [hβdef, hnvecdef] using (β.repr_self 0)
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
  have hsa : ∀ P : ℝ², signedArea2 P q1 q2 = Y P * ‖u‖ ^ 2 := by
    intro P; rw [harea_gen P q1 q2, hX_q1, hY_q1, hX_q2, hY_q2]; ring
  have hXp2 : X p2 = 0 := by
    have hdist_eq : dist p2 q1 = dist p2 q2 := by
      rw [show dist p2 q1 = t from hv2v3, show dist p2 q2 = t from hv2x]
    have hperp : p2 ∈ AffineSubspace.perpBisector q1 q2 := by
      rw [AffineSubspace.mem_perpBisector_iff_dist_eq]; simpa using hdist_eq
    have hcenter_perp : inner ℝ (p2 - M) u = 0 := by
      have h := (AffineSubspace.mem_perpBisector_iff_inner_eq_zero
        (c := p2) (p₁ := q1) (p₂ := q2)).mp hperp
      simpa [hMdef] using h
    have horth_rev : inner ℝ nvec u = 0 := by simpa [real_inner_comm] using horth
    have hinner : inner ℝ (p2 - M) u = X p2 * ‖u‖ ^ 2 := by
      calc
        inner ℝ (p2 - M) u
            = inner ℝ (X p2 • u + Y p2 • nvec) u := by rw [hsum_pt p2]
        _ = X p2 * ‖u‖ ^ 2 + Y p2 * 0 := by
              rw [inner_add_left, inner_smul_left, inner_smul_left,
                real_inner_self_eq_norm_sq, horth_rev]; simp
        _ = X p2 * ‖u‖ ^ 2 := by ring
    rw [hcenter_perp] at hinner
    rcases mul_eq_zero.mp hinner.symm with h | h
    · exact h
    · exact absurd h (ne_of_gt hu_sq_pos)
  have hsign :
      0 < signedArea2 a₃ q1 q2 * signedArea2 p2 q1 q2 := by
    rw [hq1, hq2, hp2]
    have hxI2' : x ∈ S.I2 := by rw [hq2] at hxI2; exact hxI2
    have hv2v3' : dist S.triangle.v2 S.triangle.v3 = t := by
      rw [hp2, hq1] at hv2v3; exact hv2v3
    have hv2x' : dist S.triangle.v2 x = t := by rw [hp2, hq2] at hv2x; exact hv2x
    exact Problem97.signedArea_prod_pos_trans
      (b3n9m053_same_side_of_chord_capPair S ha3I3 hxI2')
      (b3n9m053_same_side_of_chord_endpoint_thales S hxI2' hv2v3' hv2x')
  simpa [hq1, hq2, hp2] using hsign
theorem b3n9m053_v1_same_side_of_v3x_chord
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {x : ℝ²}
    (hxI2 : x ∈ S.I2) :
    0 < signedArea2 S.triangle.v1 S.triangle.v3 x *
        signedArea2 S.triangle.v2 S.triangle.v3 x := by
  classical
  have hxC2 : x ∈ S.CP.C2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).2
  have hx_ne_v3 : x ≠ S.triangle.v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1
  have hx_ne_v1 : x ≠ S.triangle.v1 := (Finset.mem_erase.mp hxI2).1
  obtain ⟨n, phi, hphi_inj, hphi_image, hneg, hnpos⟩ := b3n9m053_boundaryOrder_hneg S
  haveI : NeZero n := ⟨by omega⟩
  have hv1A : S.triangle.v1 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v1_mem
  have hv2A : S.triangle.v2 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v2_mem
  have hv3A : S.triangle.v3 ∈ Finset.univ.image phi := by rw [hphi_image]; exact S.triangle.v3_mem
  rcases Finset.mem_image.mp hv1A with ⟨i1, _, hi1⟩
  rcases Finset.mem_image.mp hv2A with ⟨i2, _, hi2⟩
  rcases Finset.mem_image.mp hv3A with ⟨i3, _, hi3⟩
  obtain ⟨psi, hpsi_inj, hpsi_image, hneg_s, hpsi_re⟩ :=
    b3n9m053_shift_boundaryOrder hphi_inj hphi_image hneg i2
  set jv2 : Fin n := i2 - i2 with hjv2def
  set jv3 : Fin n := i3 - i2 with hjv3def
  set jv1 : Fin n := i1 - i2 with hjv1def
  have hpv2 : psi jv2 = S.triangle.v2 := by rw [hjv2def, hpsi_re, hi2]
  have hpv3 : psi jv3 = S.triangle.v3 := by rw [hjv3def, hpsi_re, hi3]
  have hpv1 : psi jv1 = S.triangle.v1 := by rw [hjv1def, hpsi_re, hi1]
  have hjv2_zero : jv2 = 0 := by rw [hjv2def]; exact sub_self i2
  have hv3_ne_v2 : jv3 ≠ jv2 := fun h => S.triangle.v23_ne.symm (by rw [← hpv3, ← hpv2, h])
  have hv1_ne_v2 : jv1 ≠ jv2 := fun h => S.triangle.v12_ne (by rw [← hpv1, ← hpv2, h])
  have hv1_ne_v3 : jv1 ≠ jv3 := fun h => S.triangle.v13_ne (by rw [← hpv1, ← hpv3, h])
  have h0_lt_jv3 : jv2 < jv3 :=
    hjv2_zero ▸ Fin.pos_iff_ne_zero.mpr (fun h => hv3_ne_v2 (hjv2_zero ▸ h))
  have h0_lt_jv1 : jv2 < jv1 :=
    hjv2_zero ▸ Fin.pos_iff_ne_zero.mpr (fun h => hv1_ne_v2 (hjv2_zero ▸ h))
  have hxA : x ∈ A := S.CP.C2_subset hxC2
  by_cases h31 : jv3 < jv1
  ·
    have hC2int := b3n9m053_supportCap_interval_of_oppositeFirst_local'
      (A := A) (C := S.CP.C2) (phi := psi) (u := S.triangle.v2) (v := S.triangle.v3)
        (w := S.triangle.v1)
      hpsi_inj hpsi_image hneg_s S.CP.C2_subset
      (fun z hzA => (S.CP.arc_membership z hzA).2.1)
      S.CP.v3_mem_C2 S.CP.v1_mem_C2 hpv2 hpv3 hpv1 h0_lt_jv3 h31
    rcases (hC2int x).1 hxC2 with ⟨ix, hlo, hhi, hxq⟩
    have hix_ne_lo : ix ≠ jv3 := fun h => hx_ne_v3 (by rw [← hxq, h, hpv3])
    have hix_ne_hi : ix ≠ jv1 := fun h => hx_ne_v1 (by rw [← hxq, h, hpv1])
    have h3x : jv3 < ix := lt_of_le_of_ne hlo (Ne.symm hix_ne_lo)
    have hx1 : ix < jv1 := lt_of_le_of_ne hhi hix_ne_hi
    have hv1_side : signedArea2 S.triangle.v1 S.triangle.v3 x < 0 := by
      rw [← hpv1, ← hpv3, ← hxq]; exact b3n9m053_sa_neg_bca hneg_s h3x hx1
    have hv2_side : signedArea2 S.triangle.v2 S.triangle.v3 x < 0 := by
      rw [← hpv2, ← hpv3, ← hxq]; exact b3n9m053_sa_neg_abc hneg_s h0_lt_jv3 h3x
    exact mul_pos_of_neg_of_neg hv1_side hv2_side
  ·
    have h13 : jv1 < jv3 := lt_of_le_of_ne (le_of_not_gt h31) hv1_ne_v3
    have hC2int := b3n9m053_supportCap_interval_of_oppositeFirst_local'
      (A := A) (C := S.CP.C2) (phi := psi) (u := S.triangle.v2) (v := S.triangle.v1)
        (w := S.triangle.v3)
      hpsi_inj hpsi_image hneg_s S.CP.C2_subset
      (b3n9m053_c2_arc_swap S) S.CP.v1_mem_C2 S.CP.v3_mem_C2
      hpv2 hpv1 hpv3 h0_lt_jv1 h13
    rcases (hC2int x).1 hxC2 with ⟨ix, hlo, hhi, hxq⟩
    have hix_ne_lo : ix ≠ jv1 := fun h => hx_ne_v1 (by rw [← hxq, h, hpv1])
    have hix_ne_hi : ix ≠ jv3 := fun h => hx_ne_v3 (by rw [← hxq, h, hpv3])
    have h1x : jv1 < ix := lt_of_le_of_ne hlo (Ne.symm hix_ne_lo)
    have hx3 : ix < jv3 := lt_of_le_of_ne hhi hix_ne_hi
    have hv1_side : 0 < signedArea2 S.triangle.v1 S.triangle.v3 x := by
      rw [← hpv1, ← hpv3, ← hxq]; exact b3n9m053_sa_pos_acb hneg_s h1x hx3
    have hv2_side : 0 < signedArea2 S.triangle.v2 S.triangle.v3 x := by
      rw [← hpv2, ← hpv3, ← hxq]
      exact b3n9m053_sa_pos_acb hneg_s (lt_trans h0_lt_jv1 h1x) hx3
    exact mul_pos hv1_side hv2_side
set_option maxHeartbeats 1600000 in
theorem b3n9m053_subshapeB_clash
    {v1 v2 v3 x : ℝ²} {r t : ℝ}
    (h12 : dist v1 v2 = t) (h23 : dist v2 v3 = t)
    (hxv1 : dist x v1 = r) (hxv3 : dist x v3 = r) (hxv2 : dist x v2 = t)
    (hnonob : 0 ≤ (v3 0 - v2 0) * (v1 0 - v2 0) + (v3 1 - v2 1) * (v1 1 - v2 1))
    (hAB : signedArea2 v2 v1 v3 * signedArea2 x v1 v3 < 0) :
    r ^ 2 * t ^ 2 < signedArea2 v1 v2 v3 ^ 2 := by
  set d2 : ℝ := (v1 0 - v3 0) ^ 2 + (v1 1 - v3 1) ^ 2 with hd2def
  have hd2nonneg : 0 ≤ d2 := by rw [hd2def]; positivity
  have hnonobd : d2 ≤ 2 * t ^ 2 := by
    have e12 := dist_sq_coord v1 v2; have e23 := dist_sq_coord v2 v3
    rw [h12] at e12; rw [h23] at e23
    rw [hd2def]; nlinarith only [hnonob, e12, e23]
  have hSAx : 4 * signedArea2 x v1 v3 ^ 2 = 4 * r ^ 2 * d2 - d2 ^ 2 := by
    have ex1 := dist_sq_coord x v1; have ex3 := dist_sq_coord x v3
    rw [hxv1] at ex1; rw [hxv3] at ex3
    simp only [signedArea2]; rw [hd2def]; nlinarith only [ex1, ex3]
  have hSAv2 : 4 * signedArea2 v2 v1 v3 ^ 2 = 4 * t ^ 2 * d2 - d2 ^ 2 := by
    have e12 := dist_sq_coord v1 v2; have e23 := dist_sq_coord v2 v3
    rw [h12] at e12; rw [h23] at e23
    simp only [signedArea2]; rw [hd2def]; nlinarith only [e12, e23]
  have hdiff : (signedArea2 v2 v1 v3 - signedArea2 x v1 v3) ^ 2 = d2 * t ^ 2 := by
    have hperp : (v3 0 - v1 0) * (v2 0 - x 0) + (v3 1 - v1 1) * (v2 1 - x 1) = 0 := by
      have ex1 := dist_sq_coord x v1; have ex3 := dist_sq_coord x v3
      have e12 := dist_sq_coord v1 v2; have e23 := dist_sq_coord v2 v3
      rw [hxv1] at ex1; rw [hxv3] at ex3; rw [h12] at e12; rw [h23] at e23
      nlinarith only [ex1, ex3, e12, e23]
    have ex2 := dist_sq_coord x v2
    rw [hxv2] at ex2
    simp only [signedArea2]; rw [hd2def]; nlinarith only [ex2, hperp]
  have hsq_eq : signedArea2 v1 v2 v3 ^ 2 = signedArea2 v2 v1 v3 ^ 2 := by
    have hflip : signedArea2 v1 v2 v3 = - signedArea2 v2 v1 v3 := by
      simp only [signedArea2]; ring
    rw [hflip]; ring
  rw [hsq_eq]
  have hd2gt : d2 > 2 * r ^ 2 := by nlinarith [hSAx, hSAv2, hdiff, hAB]
  nlinarith only [hnonobd, hdiff, hd2gt, hSAv2, hAB, sq_nonneg (t ^ 2 - r ^ 2), mul_nonneg hd2nonneg hd2nonneg]

set_option maxHeartbeats 1600000 in
theorem b3n9m053_rWindow_general
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {a₁ : ℝ²} {r t : ℝ}
    (ha1I1 : a₁ ∈ S.I1)
    (hv1a1 : dist S.triangle.v1 a₁ = r)
    (hv2v3 : dist S.triangle.v2 S.triangle.v3 = t) :
    signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 ^ 2 < t ^ 2 * r ^ 2 := by
  classical
  set v1 := S.triangle.v1 with hv1def
  set v2 := S.triangle.v2 with hv2def
  set v3 := S.triangle.v3 with hv3def
  have ha1A : a₁ ∈ A :=
    S.CP.C1_subset (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha1I1))
  have ha1C1 : a₁ ∈ S.CP.C1 :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha1I1)
  have ha1ne3 : a₁ ≠ v3 := (Finset.mem_erase.mp ha1I1).1
  have ha1ne2 : a₁ ≠ v2 :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase ha1I1)).1
  have hle : signedArea2 a₁ v2 v3 * signedArea2 v1 v2 v3 ≤ 0 :=
    (S.CP.arc_membership a₁ ha1A).1.mp ha1C1
  have h2A : v2 ∈ A := S.triangle.v2_mem
  have h3A : v3 ∈ A := S.triangle.v3_mem
  have ha1SAne : signedArea2 a₁ v2 v3 ≠ 0 := by
    intro hΔ
    have hcol : Collinear ℝ ({a₁, v2, v3} : Set ℝ²) :=
      Problem97.collinear_of_signedArea2_eq_zero a₁ v2 v3 hΔ
    have hconv : ConvexIndep A := S.hconv
    rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
    · apply hconv v2 (by exact_mod_cast h2A)
      have hseg : v2 ∈ segment ℝ a₁ v3 := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro p hp
      rcases hp with rfl | hp
      · exact ⟨by exact_mod_cast ha1A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha1ne2 h⟩
      · rcases hp with rfl
        exact ⟨by exact_mod_cast h3A, by
          simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v23_ne h.symm⟩
    · apply hconv v3 (by exact_mod_cast h3A)
      have hseg : v3 ∈ segment ℝ v2 a₁ := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro p hp
      rcases hp with rfl | hp
      · exact ⟨by exact_mod_cast h2A, by
          simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v23_ne h⟩
      · rcases hp with rfl
        exact ⟨by exact_mod_cast ha1A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha1ne3 h⟩
    · apply hconv a₁ (by exact_mod_cast ha1A)
      have hseg : a₁ ∈ segment ℝ v3 v2 := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro p hp
      rcases hp with rfl | hp
      · exact ⟨by exact_mod_cast h3A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha1ne3 h.symm⟩
      · rcases hp with rfl
        exact ⟨by exact_mod_cast h2A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha1ne2 h.symm⟩
  have hv1SAne : signedArea2 v1 v2 v3 ≠ 0 := by
    have hv1O : ‖v1 - S.Packet.center‖ = S.Packet.radius :=
      S.Packet.moser_on_boundary_1
    have hv2O : ‖v2 - S.Packet.center‖ = S.Packet.radius :=
      S.Packet.moser_on_boundary_2
    have hv3O : ‖v3 - S.Packet.center‖ = S.Packet.radius :=
      S.Packet.moser_on_boundary_3
    exact MEC.signedArea2_ne_zero_of_three_dist_eq
      (by simpa [dist_eq_norm] using hv1O)
      (by simpa [dist_eq_norm] using hv2O)
      (by simpa [dist_eq_norm] using hv3O)
      S.triangle.v12_ne S.triangle.v23_ne S.triangle.v13_ne
  have hstrict : signedArea2 a₁ v2 v3 * signedArea2 v1 v2 v3 < 0 :=
    lt_of_le_of_ne hle (mul_ne_zero ha1SAne hv1SAne)
  have hcross : signedArea2 v1 v2 v3 - signedArea2 a₁ v2 v3 =
      (v2 0 - v3 0) * (a₁ 1 - v1 1) - (v2 1 - v3 1) * (a₁ 0 - v1 0) := by
    simp only [signedArea2]; ring
  have hcs : ((v2 0 - v3 0) * (a₁ 1 - v1 1) - (v2 1 - v3 1) * (a₁ 0 - v1 0)) ^ 2
      ≤ t ^ 2 * r ^ 2 := by
    have e23 := dist_sq_coord v2 v3; have e1a1 := dist_sq_coord v1 a₁
    rw [hv2v3] at e23; rw [hv1a1] at e1a1
    nlinarith only [e23, e1a1, sq_nonneg ((v2 0 - v3 0) * (a₁ 0 - v1 0) + (v2 1 - v3 1) * (a₁ 1 - v1 1))]

  have ha1sq : 0 < signedArea2 a₁ v2 v3 ^ 2 := by positivity
  have hgap : signedArea2 v1 v2 v3 ^ 2 <
      (signedArea2 v1 v2 v3 - signedArea2 a₁ v2 v3) ^ 2 := by
    nlinarith only [hstrict, ha1sq]
  rw [hcross] at hgap
  linarith [hcs, hgap]
theorem b3n9m053_cap_MNK_core {M N K : ℝ} (hKnn : 0 ≤ K) (hM0 : 0 ≤ M)
    (hDid : M ^ 2 - N ^ 2 = K - 2 * N) : 0 ≤ N + M := by
  rcases le_or_gt 0 N with hNpos | hNneg
  · linarith
  · have hMN : N ^ 2 ≤ M ^ 2 := by nlinarith only [hKnn, hDid, hNneg]
    have hge : -N ≤ M := by nlinarith only [hKnn, hDid, hNneg, hM0, hMN, sq_nonneg (M + N)]
    linarith
set_option maxHeartbeats 2000000 in
theorem b3n9m053_cap_reduced (a p BT : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hBT0 : 0 ≤ BT)
    (hBTsq : BT ^ 2 = (1 - a ^ 2) * (1 - p ^ 2))
    (hpa : a < p) (hR : 2 * p ≤ 1 + a ^ 2) :
    3 ≤ 4 * (a * p + BT) ^ 2 := by
  have hp0 : 0 ≤ p := le_of_lt (lt_of_le_of_lt ha0 hpa)
  have hapBT : 0 ≤ a * p * BT := mul_nonneg (mul_nonneg ha0 hp0) hBT0
  have hpub : p ≤ (1 + a ^ 2) / 2 := by linarith
  have hp2 : p ^ 2 ≤ ((1 + a ^ 2) / 2) ^ 2 := by nlinarith only [hR, ha0, hpa, hp0, hpub, mul_nonneg hp0 hp0]
  have hpa2 : p ^ 2 - a ^ 2 ≤ 1 / 4 := by
    nlinarith only [hp2, ha0, hpa, hR, ha1, mul_nonneg (mul_nonneg ha0 ha0) (by nlinarith [ha1, ha0] : (0 : ℝ) ≤ 2 - a ^ 2)]

  have hpa2nn : 0 ≤ p ^ 2 - a ^ 2 := by nlinarith only [ha0, hpa, hp0]
  obtain ⟨M, hMdef⟩ : ∃ M, M = 8 * (a * p * BT) := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, N = 8 * a ^ 2 * p ^ 2 - 4 * a ^ 2 - 4 * p ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = 1 - 16 * (p ^ 2 - a ^ 2) ^ 2 := ⟨_, rfl⟩
  have hKnn : 0 ≤ K := by rw [hKdef]; nlinarith only [hpa2, hpa2nn]
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith [hapBT]
  have hid' : 4 * (a * p + BT) ^ 2 - 3 = N + M := by
    rw [hMdef, hNdef]; linear_combination 4 * hBTsq
  have hDid' : M ^ 2 - N ^ 2 = K - 2 * N := by
    rw [hMdef, hNdef, hKdef]; linear_combination (64 * a ^ 2 * p ^ 2) * hBTsq
  have := b3n9m053_cap_MNK_core hKnn hM0 hDid'
  linarith [hid', this]
set_option maxHeartbeats 2000000 in
theorem b3n9m053_cap_scalar (a beta p sig : ℝ)
    (h1 : a ^ 2 + beta ^ 2 = 1) (h2 : p ^ 2 + sig ^ 2 = 1)
    (ha : 0 ≤ a) (ha1 : a < 1)
    (hrwin : 2 * p ≤ 1 + a ^ 2)
    (harcx : beta * (beta * (1 - p) - sig * (1 - a)) < 0) :
    3 ≤ 4 * (a * p + beta * sig) ^ 2 ∧ 0 ≤ a * p + beta * sig := by
  have h1a : 0 < 1 - a := by linarith
  have hbsig : 0 ≤ beta * sig := by
    have hk : beta ^ 2 * (1 - p) ≤ beta * sig * (1 - a) := by nlinarith only [harcx]
    have hb2 : 0 ≤ beta ^ 2 * (1 - p) := by nlinarith only [h1, hrwin, sq_nonneg beta, h2, sq_nonneg sig]
    nlinarith only [harcx, hb2, h1, hk, h1a, mul_pos h1a h1a]
  have hpa : a < p := by
    by_contra hlt
    push_neg at hlt
    have hbsb : beta ^ 2 ≤ beta * sig := by
      have hstep : beta ^ 2 * (1 - a) ≤ beta * sig * (1 - a) := by
        nlinarith only [harcx, hlt, sq_nonneg beta]
      exact le_of_mul_le_mul_right (by linarith [hstep]) h1a
    have hb2 : 0 < beta ^ 2 := by nlinarith only [h1, ha1, ha]
    have hsig2 : beta ^ 2 ≤ sig ^ 2 := by nlinarith only [hbsb, hb2, sq_nonneg (beta * sig - beta ^ 2)]
    nlinarith only [harcx, h1, h2, hlt, ha, hbsb, hb2, hsig2, sq_nonneg (sig - beta), sq_nonneg (sig + beta), mul_pos hb2 hb2, mul_nonneg (le_of_lt hb2) (sub_nonneg.mpr hsig2), sq_nonneg (p - a)]

  have hBTsq : (beta * sig) ^ 2 = (1 - a ^ 2) * (1 - p ^ 2) := by
    have e1 : beta ^ 2 = 1 - a ^ 2 := by linarith
    have e2 : sig ^ 2 = 1 - p ^ 2 := by linarith
    rw [mul_pow, e1, e2]
  have hp0 : 0 ≤ p := le_of_lt (lt_of_le_of_lt ha hpa)
  exact ⟨b3n9m053_cap_reduced a p (beta * sig) ha (le_of_lt ha1) hbsig hBTsq hpa hrwin,
    add_nonneg (mul_nonneg ha hp0) hbsig⟩
theorem b3n9m053_cap_goal_pos (cc Qx Qq t s3 : ℝ)
    (ht : 0 < t) (hs3 : s3 ^ 2 = 3) (hs3pos : 0 < s3)
    (hcc : s3 ≤ 2 * cc)
    (hQq : Qq ^ 2 = 3 * t ^ 4 / 4) (hQx : Qx ^ 2 = (1 - cc ^ 2) * t ^ 4) :
    0 < cc * t ^ 4 - 2 * Qq * Qx + t ^ 4 := by
  have ht4 : 0 < t ^ 4 := by positivity
  have hcc2 : 3 / 4 ≤ cc ^ 2 := by nlinarith only [hs3, hs3pos, hcc]
  have h1cc : 1 - cc ^ 2 ≤ 1 / 4 := by linarith
  have hpos : 0 < (cc + 1) * t ^ 4 := by nlinarith only [ht4, hcc, hs3pos, hQq, hcc2]
  have hsqstrict : (2 * Qq * Qx) ^ 2 < ((cc + 1) * t ^ 4) ^ 2 := by
    have e : (2 * Qq * Qx) ^ 2 = 3 * (1 - cc ^ 2) * t ^ 8 := by
      have h2 : (2 * Qq * Qx) ^ 2 = 4 * (Qq ^ 2) * (Qx ^ 2) := by ring
      rw [h2, hQq, hQx]; ring
    rw [e]
    nlinarith only [ht4, hs3pos, hcc, hcc2, h1cc, mul_pos ht4 ht4]
  have hlt : 2 * Qq * Qx < (cc + 1) * t ^ 4 := by
    nlinarith only [hpos, hsqstrict, sq_nonneg (2 * Qq * Qx - (cc + 1) * t ^ 4)]
  linarith [hlt]
set_option maxHeartbeats 4000000 in
theorem b3n9m053_subshapeB_L1_residual
    {v1 v2 v3 x q3 : ℝ²} {r t : ℝ}
    (ht : 0 < t) (hr : 0 < r)
    (hv2v3 : dist v2 v3 = t) (hv2v1 : dist v2 v1 = t) (hv2x : dist v2 x = t)
    (hv2q3 : dist v2 q3 = t) (hv3q3 : dist v3 q3 = t) (hv1x : dist v1 x = r)
    (hnonob : 0 ≤ inner ℝ (v3 - v2) (v1 - v2))
    (hrwin : signedArea2 v1 v2 v3 ^ 2 < t ^ 2 * r ^ 2)
    (harcx_strict : signedArea2 x v3 v1 * signedArea2 v2 v3 v1 < 0)
    (hbne : signedArea2 v2 v3 v1 ≠ 0) (hx_ne_v1 : x ≠ v1) :
    0 < inner ℝ (v3 - q3) (x - q3) := by
  classical
  set t2 : ℝ := t ^ 2 with ht2def
  have ht2pos : 0 < t2 := by positivity
  have hnv3 : inner ℝ (v3 - v2) (v3 - v2) = t2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hv2v3]
  have hnv1 : inner ℝ (v1 - v2) (v1 - v2) = t2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hv2v1]
  have hnx : inner ℝ (x - v2) (x - v2) = t2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hv2x]
  have hnq : inner ℝ (q3 - v2) (q3 - v2) = t2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hv2q3]
  have hnv3q : inner ℝ (v3 - q3) (v3 - q3) = t2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hv3q3]
  set Ia : ℝ := inner ℝ (v1 - v2) (v3 - v2) with hIadef
  set Ip : ℝ := inner ℝ (x - v2) (v1 - v2) with hIpdef
  set Ic : ℝ := inner ℝ (x - v2) (v3 - v2) with hIcdef
  set bcr : ℝ := signedArea2 v2 v3 v1 with hbdef
  set scr : ℝ := signedArea2 v1 v2 x with hsdef
  set Qx : ℝ := signedArea2 v2 v3 x with hQxdef
  set Qq : ℝ := signedArea2 v2 v3 q3 with hQqdef
  have hLag1' : Ia ^ 2 + bcr ^ 2
      = inner ℝ (v1 - v2) (v1 - v2) * inner ℝ (v3 - v2) (v3 - v2) := by
    rw [hIadef, hbdef]
    simp only [signedArea2, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_two, PiLp.sub_apply]; ring
  have hLag1 : Ia ^ 2 + bcr ^ 2 = t2 * t2 := by rw [hLag1', hnv1, hnv3]
  have hLagx' : Ip ^ 2 + scr ^ 2
      = inner ℝ (x - v2) (x - v2) * inner ℝ (v1 - v2) (v1 - v2) := by
    rw [hIpdef, hsdef]
    simp only [signedArea2, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_two, PiLp.sub_apply]; ring
  have hLagx : Ip ^ 2 + scr ^ 2 = t2 * t2 := by rw [hLagx', hnx, hnv1]
  have hLagc' : Ic ^ 2 + Qx ^ 2
      = inner ℝ (x - v2) (x - v2) * inner ℝ (v3 - v2) (v3 - v2) := by
    rw [hIcdef, hQxdef]
    simp only [signedArea2, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_two, PiLp.sub_apply]; ring
  have hLagc : Ic ^ 2 + Qx ^ 2 = t2 * t2 := by rw [hLagc', hnx, hnv3]
  have hrot' : Ic * inner ℝ (v1 - v2) (v1 - v2) = Ia * Ip + bcr * scr := by
    rw [hIadef, hIpdef, hIcdef, hbdef, hsdef]
    simp only [signedArea2, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_two, PiLp.sub_apply]; ring
  have hrot : Ic * t2 = Ia * Ip + bcr * scr := by rw [← hnv1]; exact hrot'
  have hadd : signedArea2 x v3 v1 = bcr - scr - Qx := by
    simp only [hbdef, hsdef, hQxdef, signedArea2]; ring
  have hgoalid : 2 * t2 * (inner ℝ (v3 - q3) (x - q3)) = Ic * t2 - 2 * Qq * Qx + t2 ^ 2 := by
    rw [hIcdef, hQqdef, hQxdef]
    simp only [signedArea2, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_two, PiLp.sub_apply] at hnq hnv3 hnv3q ⊢
    set IP3PX := (v3 0 - v2 0) * (x 0 - v2 0) + (v3 1 - v2 1) * (x 1 - v2 1)
    set IPQPX := (q3 0 - v2 0) * (x 0 - v2 0) + (q3 1 - v2 1) * (x 1 - v2 1)
    linear_combination (t2 - IP3PX) * hnq + (-IP3PX + 2 * IPQPX - t2) * hnv3 + (IP3PX + t2) * hnv3q
  have hQqsq : 4 * Qq ^ 2 = 3 * t2 ^ 2 := by
    rw [hQqdef]
    simp only [signedArea2, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_two, PiLp.sub_apply] at hnq hnv3 hnv3q ⊢
    set IP3P3 := (v3 0 - v2 0) * (v3 0 - v2 0) + (v3 1 - v2 1) * (v3 1 - v2 1)
    set IP3PQ := (v3 0 - v2 0) * (q3 0 - v2 0) + (v3 1 - v2 1) * (q3 1 - v2 1)
    linear_combination (4 * IP3P3 - 2 * IP3PQ - t2) * hnq + (-2 * IP3PQ + 3 * t2) * hnv3 +
      (2 * IP3PQ + t2) * hnv3q
  set a : ℝ := Ia / t2 with hadef
  set beta : ℝ := bcr / t2 with hbetadef
  set p : ℝ := Ip / t2 with hpdef
  set sig : ℝ := scr / t2 with hsigdef
  set cc : ℝ := Ic / t2 with hccdef
  have ht2ne : t2 ≠ 0 := ne_of_gt ht2pos
  have h1 : a ^ 2 + beta ^ 2 = 1 := by
    rw [hadef, hbetadef, div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity)]
    rw [hLag1]; ring
  have h2 : p ^ 2 + sig ^ 2 = 1 := by
    rw [hpdef, hsigdef, div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity)]
    rw [hLagx]; ring
  have hcceq : cc = a * p + beta * sig := by
    rw [hccdef, hadef, hbetadef, hpdef, hsigdef]
    have key : Ia / t2 * (Ip / t2) + bcr / t2 * (scr / t2) = (Ia * Ip + bcr * scr) / t2 ^ 2 := by
      field_simp
    rw [key, ← hrot]
    field_simp
  have haIa : 0 ≤ Ia := by rw [hIadef]; rw [real_inner_comm]; exact hnonob
  have ha : 0 ≤ a := by rw [hadef]; exact div_nonneg haIa (le_of_lt ht2pos)
  have hbetane : beta ≠ 0 := by
    rw [hbetadef]; exact div_ne_zero hbne ht2ne
  have ha1 : a < 1 := by
    have hb2pos : 0 < beta ^ 2 := by positivity
    nlinarith only [h1, hb2pos, ha]
  have hrwin' : 2 * p ≤ 1 + a ^ 2 := by
    have hSAeq : signedArea2 v1 v2 v3 = bcr := by
      simp only [hbdef, signedArea2]; ring
    have hr2 : r ^ 2 = t2 * (2 - 2 * p) := by
      have hxv1 : inner ℝ (x - v1) (x - v1) = r ^ 2 := by
        rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hv1x]
      have hexp : inner ℝ (x - v1) (x - v1)
          = inner ℝ (x - v2) (x - v2) + inner ℝ (v1 - v2) (v1 - v2)
            - 2 * inner ℝ (x - v2) (v1 - v2) := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
          Fin.sum_univ_two, PiLp.sub_apply]; ring
      rw [hexp, hnx, hnv1, ← hIpdef] at hxv1
      rw [hpdef]; field_simp; linear_combination -hxv1
    rw [hSAeq] at hrwin
    have hbeta2 : beta ^ 2 < 2 - 2 * p := by
      rw [hbetadef, div_pow]
      rw [div_lt_iff₀ (by positivity)]
      rw [hr2] at hrwin
      nlinarith only [hrwin, ht2pos]
    nlinarith only [h1, hbeta2]
  have hbcr : bcr = beta * t2 := by rw [hbetadef]; field_simp
  have hIpr : Ip = p * t2 := by rw [hpdef]; field_simp
  have hscr : scr = sig * t2 := by rw [hsigdef]; field_simp
  have hIar : Ia = a * t2 := by rw [hadef]; field_simp
  have harcx' : beta * (beta * (1 - p) - sig * (1 - a)) < 0 := by
    have hQxrot' : Qx * inner ℝ (v1 - v2) (v1 - v2) = bcr * Ip - Ia * scr := by
      rw [hIadef, hIpdef, hbdef, hsdef, hQxdef]
      simp only [signedArea2, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_two, PiLp.sub_apply]; ring
    have hQxrot : Qx * t2 = bcr * Ip - Ia * scr := by rw [← hnv1]; exact hQxrot'
    have hQ : Qx * t2 = (beta * p - a * sig) * t2 ^ 2 := by
      rw [hQxrot, hbcr, hIpr, hscr, hIar]; ring
    have hQx : Qx = (beta * p - a * sig) * t2 := by
      have hcancel : Qx * t2 = ((beta * p - a * sig) * t2) * t2 := by rw [hQ]; ring
      exact mul_right_cancel₀ ht2ne hcancel
    have hkey : signedArea2 x v3 v1 * bcr
        = t2 ^ 2 * (beta * (beta * (1 - p) - sig * (1 - a))) := by
      rw [hadd, hbcr, hscr, hQx]; ring
    rw [hbdef] at harcx_strict
    have hpos : 0 < t2 ^ 2 := by positivity
    nlinarith only [harcx_strict, hkey, hpos]
  obtain ⟨h4cc, hcc0⟩ := b3n9m053_cap_scalar a beta p sig h1 h2 ha ha1 hrwin' harcx'
  rw [← hcceq] at h4cc hcc0
  set s3 : ℝ := Real.sqrt 3 with hs3def
  have hs3sq : s3 ^ 2 = 3 := by rw [hs3def, Real.sq_sqrt]; norm_num
  have hs3pos : 0 < s3 := by rw [hs3def]; exact Real.sqrt_pos.mpr (by norm_num)
  have hcc_ge : s3 ≤ 2 * cc := by
    have h2cc : 0 ≤ 2 * cc := by linarith [hcc0]
    nlinarith only [hcc0, h4cc, hs3pos, hs3sq, sq_nonneg (2 * cc - s3), sq_nonneg (2 * cc + s3)]
  have hQxsq : Qx ^ 2 = (1 - cc ^ 2) * t ^ 4 := by
    have hcct2 : Ic = cc * t2 := by rw [hccdef]; field_simp
    have : Qx ^ 2 = t2 * t2 - Ic ^ 2 := by linarith [hLagc]
    rw [this, hcct2, ht2def]; ring
  have hQqsq' : Qq ^ 2 = 3 * t ^ 4 / 4 := by rw [ht2def] at hQqsq; nlinarith only [hQqsq]
  have hpos := b3n9m053_cap_goal_pos cc Qx Qq t s3 ht hs3sq hs3pos hcc_ge hQqsq' hQxsq
  have hcct4 : cc * t ^ 4 - 2 * Qq * Qx + t ^ 4 = 2 * t2 * (inner ℝ (v3 - q3) (x - q3)) := by
    rw [hgoalid]
    have hcct2 : Ic = cc * t2 := by rw [hccdef]; field_simp
    rw [hcct2, ht2def]; ring
  rw [hcct4] at hpos
  have h2t2 : 0 < 2 * t2 := by positivity
  exact (mul_pos_iff_of_pos_left h2t2).mp hpos
set_option maxHeartbeats 4000000 in
theorem b3n9m053_layer4_subshapeB_kill
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S)
    {x y q₃ a₁ b₁ a₃ b₃ : ℝ²} {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t)
    (hxI2 : x ∈ S.I2) (hyI3 : y ∈ S.I3) (ha3I3 : a₃ ∈ S.I3) (hb3I3 : b₃ ∈ S.I3)
    (hI1eq : S.I1 = ({a₁, b₁} : Finset ℝ²)) (hI3eq : S.I3 = ({a₃, b₃} : Finset ℝ²))
    (hxA : x ∈ A)
    (ha1I1 : a₁ ∈ S.I1) (hv1a1 : dist S.triangle.v1 a₁ = r)
    (hb1I1 : b₁ ∈ S.I1) (hv1b1 : dist S.triangle.v1 b₁ = r)
    (hv1x : dist S.triangle.v1 x = r) (hv1y : dist S.triangle.v1 y = r)
    (hv2x : dist S.triangle.v2 x = t) (hv3y : dist S.triangle.v3 y = t)
    (hv3a3 : dist S.triangle.v3 a₃ = t) (hv3b3 : dist S.triangle.v3 b₃ = t)
    (hv2v3 : dist S.triangle.v2 S.triangle.v3 = t)
    (hv2v1 : dist S.triangle.v2 S.triangle.v1 = t)
    (hv2q3 : dist S.triangle.v2 q₃ = t) (hv3q3 : dist S.triangle.v3 q₃ = t)
    (hq3I2 : q₃ ∈ S.I2)
    (horient : 0 < signedArea2 x S.triangle.v1 S.triangle.v2 *
                 signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2) :
    False := by
  classical
  obtain ⟨ρ, hρpos, hKcard⟩ := S.hK4 x hxA
  set K : Finset ℝ² := A.filter (fun q => dist x q = ρ) with hKdef
  have hKcard' : 4 ≤ K.card := hKcard
  have hL1 : 0 < signedArea2 q₃ S.triangle.v3 x *
      signedArea2 S.triangle.v2 S.triangle.v3 x := by
    set v1 := S.triangle.v1 with hv1def
    set v2 := S.triangle.v2 with hv2def
    set v3 := S.triangle.v3 with hv3def
    have hx_ne_v3 : x ≠ v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1
    have heqnorm : ‖v3 - v2‖ = ‖x - v2‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, dist_comm v3 v2, dist_comm x v2, hv2v3, hv2x]
    refine signedArea_prod_pos_of_inner_midpoint_pos heqnorm hx_ne_v3 ?_
    have hv3O : ‖v3 - v2‖ = ‖q₃ - v2‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, dist_comm v3 v2, dist_comm q₃ v2, hv2v3, hv2q3]
    have hxO : ‖x - v2‖ = ‖q₃ - v2‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, dist_comm x v2, dist_comm q₃ v2, hv2x, hv2q3]
    have hangle : inner ℝ (v3 - q₃) (x - q₃)
        = 2 * inner ℝ (midpoint ℝ v3 x - v2) (midpoint ℝ v3 x - q₃) :=
      inner_chord_eq_two_mul_inner_midpoint hv3O hxO
    have hcomm : inner ℝ (midpoint ℝ v3 x - q₃) (midpoint ℝ v3 x - v2)
        = inner ℝ (midpoint ℝ v3 x - v2) (midpoint ℝ v3 x - q₃) := real_inner_comm _ _
    have hhalf : inner ℝ (midpoint ℝ v3 x - q₃) (midpoint ℝ v3 x - v2)
        = (1 / 2 : ℝ) * inner ℝ (v3 - q₃) (x - q₃) := by rw [hcomm]; linarith [hangle]
    rw [hhalf]
    suffices hresidual : 0 < inner ℝ (v3 - q₃) (x - q₃) by linarith
    have hrwin : signedArea2 v1 v2 v3 ^ 2 < t ^ 2 * r ^ 2 :=
      b3n9m053_rWindow_general S ha1I1 hv1a1 hv2v3
    have hnonob : 0 ≤ inner ℝ (v3 - v2) (v1 - v2) := S.Packet.inner_at_v2
    have harcx : signedArea2 x v3 v1 * signedArea2 v2 v3 v1 ≤ 0 := by
      have haC2 : x ∈ S.CP.C2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).2
      have h := ((S.CP.arc_membership x hxA).2.1).mp haC2
      simpa [Problem97.OnArcOpposite] using h
    have hx_ne_v1 : x ≠ v1 := (Finset.mem_erase.mp hxI2).1
    have hbne : signedArea2 v2 v3 v1 ≠ 0 := by
      have hv1O : ‖v1 - S.Packet.center‖ = S.Packet.radius := S.Packet.moser_on_boundary_1
      have hv2O : ‖v2 - S.Packet.center‖ = S.Packet.radius := S.Packet.moser_on_boundary_2
      have hv3O : ‖v3 - S.Packet.center‖ = S.Packet.radius := S.Packet.moser_on_boundary_3
      have h132 : signedArea2 v1 v2 v3 ≠ 0 :=
        MEC.signedArea2_ne_zero_of_three_dist_eq
          (by simpa [dist_eq_norm] using hv1O) (by simpa [dist_eq_norm] using hv2O)
          (by simpa [dist_eq_norm] using hv3O)
          S.triangle.v12_ne S.triangle.v23_ne S.triangle.v13_ne
      intro hb0; apply h132
      have : signedArea2 v1 v2 v3 = signedArea2 v2 v3 v1 := by
        simp only [signedArea2]; ring
      rw [this]; exact hb0
    have hxSAne : signedArea2 x v3 v1 ≠ 0 := by
      intro hΔ
      have hcol : Collinear ℝ ({x, v3, v1} : Set ℝ²) :=
        Problem97.collinear_of_signedArea2_eq_zero x v3 v1 hΔ
      have hconv : ConvexIndep A := S.hconv
      have hxne1 : x ≠ v1 := hx_ne_v1
      have hxne3 : x ≠ v3 := hx_ne_v3
      have hv1ne3 : v1 ≠ v3 := S.triangle.v13_ne
      have h3A : v3 ∈ A := S.triangle.v3_mem
      have h1A : v1 ∈ A := S.triangle.v1_mem
      rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
      · apply hconv v3 (by exact_mod_cast h3A)
        have hseg : v3 ∈ segment ℝ x v1 := hw.mem_segment
        rw [← convexHull_pair] at hseg
        refine convexHull_mono ?_ hseg
        intro q hq
        rcases hq with rfl | hq
        · exact ⟨by exact_mod_cast hxA, by
            simp only [Set.mem_singleton_iff]; exact fun h => hxne3 h⟩
        · rcases hq with rfl
          exact ⟨by exact_mod_cast h1A, by
            simp only [Set.mem_singleton_iff]; exact fun h => hv1ne3 h⟩
      · apply hconv v1 (by exact_mod_cast h1A)
        have hseg : v1 ∈ segment ℝ v3 x := hw.mem_segment
        rw [← convexHull_pair] at hseg
        refine convexHull_mono ?_ hseg
        intro q hq
        rcases hq with rfl | hq
        · exact ⟨by exact_mod_cast h3A, by
            simp only [Set.mem_singleton_iff]; exact fun h => hv1ne3 h.symm⟩
        · rcases hq with rfl
          exact ⟨by exact_mod_cast hxA, by
            simp only [Set.mem_singleton_iff]; exact fun h => hxne1 h⟩
      · apply hconv x (by exact_mod_cast hxA)
        have hseg : x ∈ segment ℝ v1 v3 := hw.mem_segment
        rw [← convexHull_pair] at hseg
        refine convexHull_mono ?_ hseg
        intro q hq
        rcases hq with rfl | hq
        · exact ⟨by exact_mod_cast h1A, by
            simp only [Set.mem_singleton_iff]; exact fun h => hxne1 h.symm⟩
        · rcases hq with rfl
          exact ⟨by exact_mod_cast h3A, by
            simp only [Set.mem_singleton_iff]; exact fun h => hxne3 h.symm⟩
    have harcx_strict : signedArea2 x v3 v1 * signedArea2 v2 v3 v1 < 0 :=
      lt_of_le_of_ne harcx (mul_ne_zero hxSAne hbne)
    exact b3n9m053_subshapeB_L1_residual ht hr hv2v3 hv2v1 hv2x hv2q3 hv3q3 hv1x
      hnonob hrwin harcx_strict hbne hx_ne_v1
  have hcertA3 : 0 < signedArea2 a₃ S.triangle.v3 x *
      signedArea2 S.triangle.v2 S.triangle.v3 x :=
    b3n9m053_c3_same_side_of_v3x_chord S ha3I3 hxI2 hv2v3 hv2x ht
  have hcertB3 : 0 < signedArea2 b₃ S.triangle.v3 x *
      signedArea2 S.triangle.v2 S.triangle.v3 x :=
    b3n9m053_c3_same_side_of_v3x_chord S hb3I3 hxI2 hv2v3 hv2x ht
  have hcertA1 : 0 < signedArea2 a₁ S.triangle.v1 x *
      signedArea2 S.triangle.v3 S.triangle.v1 x :=
    b3n9m053_c1_same_side_of_v1x_chord S ha1I1 hxI2
  have hcertB1 : 0 < signedArea2 b₁ S.triangle.v1 x *
      signedArea2 S.triangle.v3 S.triangle.v1 x :=
    b3n9m053_c1_same_side_of_v1x_chord S hb1I1 hxI2
  have hSAv2ne : signedArea2 S.triangle.v2 S.triangle.v3 x ≠ 0 := by
    intro h; rw [h, mul_zero] at hL1; exact (lt_irrefl 0) hL1
  have hxq3 : x ≠ q₃ := by
    intro h; rw [← h] at hL1
    simp only [signedArea2] at hL1; nlinarith only [hL1]
  have hI2eq : S.I2 = ({x, q₃} : Finset ℝ²) := by
    have hcard : S.I2.card = 2 := (p2mCoreSupport S).I2_card_eq_two
    have hsub : ({x, q₃} : Finset ℝ²) ⊆ S.I2 := by
      intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> assumption
    have hcard2 : ({x, q₃} : Finset ℝ²).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hxq3]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard2])).symm
  have hxnotK : x ∉ K := by
    rw [hKdef, Finset.mem_filter]; rintro ⟨-, hd⟩
    rw [dist_self] at hd; exact (ne_of_lt hρpos) hd
  set P1 : Finset ℝ² := {S.triangle.v2, q₃, a₃, b₃} with hP1def
  set P2 : Finset ℝ² := {a₁, b₁} with hP2def
  have hsieveP1 : (P1.filter (fun p => dist p x = ρ)).card ≤ 1 := by
    apply b3n9m053_sieve_at_most_one_on_xcircle (c := S.triangle.v3) (τ := t)
      (σ := signedArea2 S.triangle.v2 S.triangle.v3 x)
    · intro p hp
      rw [hP1def] at hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl|rfl|rfl|rfl
      · exact hv2v3
      · rw [dist_comm]; exact hv3q3
      · rw [dist_comm]; exact hv3a3
      · rw [dist_comm]; exact hv3b3
    · intro p hp
      rw [hP1def] at hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl|rfl|rfl|rfl
      · exact mul_self_pos.mpr hSAv2ne
      · exact hL1
      · exact hcertA3
      · exact hcertB3
  have hsieveP2 : (P2.filter (fun p => dist p x = ρ)).card ≤ 1 := by
    apply b3n9m053_sieve_at_most_one_on_xcircle (c := S.triangle.v1) (τ := r)
      (σ := signedArea2 S.triangle.v3 S.triangle.v1 x)
    · intro p hp
      rw [hP2def] at hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl|rfl
      · rw [dist_comm]; exact hv1a1
      · rw [dist_comm]; exact hv1b1
    · intro p hp
      rw [hP2def] at hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl|rfl
      · exact hcertA1
      · exact hcertB1
  have hKP1 : (K ∩ P1).card ≤ 1 := by
    refine le_trans (Finset.card_le_card ?_) hsieveP1
    intro q hq; rcases Finset.mem_inter.mp hq with ⟨hqK, hqP1⟩
    rw [Finset.mem_filter]; refine ⟨hqP1, ?_⟩
    have hd : dist x q = ρ := by rw [hKdef, Finset.mem_filter] at hqK; exact hqK.2
    rw [dist_comm]; exact hd
  have hKP2 : (K ∩ P2).card ≤ 1 := by
    refine le_trans (Finset.card_le_card ?_) hsieveP2
    intro q hq; rcases Finset.mem_inter.mp hq with ⟨hqK, hqP2⟩
    rw [Finset.mem_filter]; refine ⟨hqP2, ?_⟩
    have hd : dist x q = ρ := by rw [hKdef, Finset.mem_filter] at hqK; exact hqK.2
    rw [dist_comm]; exact hd
  have hAcover : A ⊆ ({S.triangle.v1, S.triangle.v2, S.triangle.v3} : Finset ℝ²)
      ∪ S.I1 ∪ S.I2 ∪ S.I3 := by
    intro p hpA
    by_cases hv1 : p = S.triangle.v1
    · subst hv1; simp
    by_cases hv2 : p = S.triangle.v2
    · subst hv2; simp
    by_cases hv3 : p = S.triangle.v3
    · subst hv3; simp
    have hnm : p ∉ S.triangle.verts := by
      simp only [Problem97.MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hv1, hv2, hv3⟩
    have hone := S.CP.nonmoser_in_one p hpA hnm
    by_cases hC1 : p ∈ S.CP.C1
    · have hpI1 : p ∈ S.I1 := by
        rw [show S.I1 = (S.CP.C1.erase S.triangle.v2).erase S.triangle.v3 from rfl]
        rw [Finset.mem_erase, Finset.mem_erase]; exact ⟨hv3, hv2, hC1⟩
      simp [hpI1]
    by_cases hC2 : p ∈ S.CP.C2
    · have hpI2 : p ∈ S.I2 := by
        rw [show S.I2 = (S.CP.C2.erase S.triangle.v3).erase S.triangle.v1 from rfl]
        rw [Finset.mem_erase, Finset.mem_erase]; exact ⟨hv1, hv3, hC2⟩
      simp [hpI2]
    by_cases hC3 : p ∈ S.CP.C3
    · have hpI3 : p ∈ S.I3 := by
        rw [show S.I3 = (S.CP.C3.erase S.triangle.v1).erase S.triangle.v2 from rfl]
        rw [Finset.mem_erase, Finset.mem_erase]; exact ⟨hv2, hv1, hC3⟩
      simp [hpI3]
    · exfalso; simp only [hC1, hC2, hC3, if_false] at hone; simp at hone
  have hcover : ∀ q ∈ A, q ≠ S.triangle.v1 → q ≠ S.triangle.v3 → q ≠ x →
      q ∈ P1 ∨ q ∈ P2 := by
    intro q hqA hqv1 hqv3 hqx
    have hq9 := hAcover hqA
    rcases Finset.mem_union.mp hq9 with hq789 | hI3mem
    · rcases Finset.mem_union.mp hq789 with hq456 | hI2mem
      · rcases Finset.mem_union.mp hq456 with hverts | hI1mem
        ·
          simp only [Finset.mem_insert, Finset.mem_singleton] at hverts
          rcases hverts with hv1 | hv2 | hv3
          · exact absurd hv1 hqv1
          · exact Or.inl (by rw [hP1def]; simp [hv2])
          · exact absurd hv3 hqv3
        ·
          right; rw [← hI1eq]; exact hI1mem
      ·
        rw [hI2eq] at hI2mem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hI2mem
        rcases hI2mem with hxc | hq3c
        · exact absurd hxc hqx
        · exact Or.inl (by rw [hP1def]; simp [hq3c])
    ·
      left; rw [hP1def]; rw [hI3eq] at hI3mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hI3mem ⊢
      tauto
  have hKsub : K ⊆ A := by rw [hKdef]; exact Finset.filter_subset _ _
  set T : Finset ℝ² := {S.triangle.v1, S.triangle.v3} with hTdef
  have hsubT : K \ T ⊆ (K ∩ P1) ∪ (K ∩ P2) := by
    intro q hq; rcases Finset.mem_sdiff.mp hq with ⟨hqK, hqT⟩
    have hqA : q ∈ A := hKsub hqK
    have hqv1 : q ≠ S.triangle.v1 := by intro h; exact hqT (by rw [hTdef, h]; simp)
    have hqv3 : q ≠ S.triangle.v3 := by intro h; exact hqT (by rw [hTdef, h]; simp)
    have hqx : q ≠ x := by intro h; exact hxnotK (h ▸ hqK)
    rcases hcover q hqA hqv1 hqv3 hqx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hqK, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hqK, h⟩)
  have hcard_sdiff : (K \ T).card ≤ 2 := by
    calc (K \ T).card ≤ ((K ∩ P1) ∪ (K ∩ P2)).card := Finset.card_le_card hsubT
      _ ≤ (K ∩ P1).card + (K ∩ P2).card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have hsplit : (K \ T).card + (K ∩ T).card = K.card := Finset.card_sdiff_add_card_inter K T
  have hTcard : T.card = 2 := by
    rw [hTdef, Finset.card_insert_of_notMem (by simp [S.triangle.v13_ne]), Finset.card_singleton]
  have hinterT : (K ∩ T) = T := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    have hle : (K ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have hTsubK : T ⊆ K := by
    intro q hq; have hqKT : q ∈ K ∩ T := by rw [hinterT]; exact hq
    exact (Finset.mem_inter.mp hqKT).1
  have hv1mem : S.triangle.v1 ∈ K := hTsubK (by rw [hTdef]; simp)
  have hv3mem : S.triangle.v3 ∈ K := hTsubK (by rw [hTdef]; simp)
  have hv1K : dist x S.triangle.v1 = ρ := by
    rw [hKdef, Finset.mem_filter] at hv1mem; exact hv1mem.2
  have hv3K : dist x S.triangle.v3 = ρ := by
    rw [hKdef, Finset.mem_filter] at hv3mem; exact hv3mem.2
  have hρr : ρ = r := by rw [← hv1K, dist_comm]; exact hv1x
  have hxv1 : dist x S.triangle.v1 = r := by rw [hv1K, hρr]
  have hxv3 : dist x S.triangle.v3 = r := by rw [hv3K, hρr]
  have hnonob : 0 ≤ (S.triangle.v3 0 - S.triangle.v2 0) * (S.triangle.v1 0 - S.triangle.v2 0) +
      (S.triangle.v3 1 - S.triangle.v2 1) * (S.triangle.v1 1 - S.triangle.v2 1) := by
    have h := S.Packet.inner_at_v2
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.vec2_dotProduct] at h
    simpa [mul_comm] using h
  have hAB : signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 *
      signedArea2 x S.triangle.v1 S.triangle.v3 < 0 := by
    have haC2 : x ∈ S.CP.C2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).2
    have hx_ne_v1 : x ≠ S.triangle.v1 := (Finset.mem_erase.mp hxI2).1
    have hx_ne_v3 : x ≠ S.triangle.v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1
    have harc_le : signedArea2 x S.triangle.v3 S.triangle.v1 *
        signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 ≤ 0 := by
      have h := ((S.CP.arc_membership x hxA).2.1).mp haC2
      simpa [Problem97.OnArcOpposite] using h
    have hxv3v1_ne : signedArea2 x S.triangle.v3 S.triangle.v1 ≠ 0 := by
      intro hΔ
      have hcol : Collinear ℝ ({x, S.triangle.v3, S.triangle.v1} : Set ℝ²) :=
        Problem97.collinear_of_signedArea2_eq_zero x S.triangle.v3 S.triangle.v1 hΔ
      have hconv : ConvexIndep A := S.hconv
      have h3A : S.triangle.v3 ∈ A := S.triangle.v3_mem
      have h1A : S.triangle.v1 ∈ A := S.triangle.v1_mem
      rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
      · apply hconv S.triangle.v3 (by exact_mod_cast h3A)
        have hseg : S.triangle.v3 ∈ segment ℝ x S.triangle.v1 := hw.mem_segment
        rw [← convexHull_pair] at hseg
        refine convexHull_mono ?_ hseg
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨by exact_mod_cast hxA, by
            simp only [Set.mem_singleton_iff]; exact fun h => hx_ne_v3 h⟩
        · rcases hz with rfl
          exact ⟨by exact_mod_cast h1A, by
            simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v13_ne h⟩
      · apply hconv S.triangle.v1 (by exact_mod_cast h1A)
        have hseg : S.triangle.v1 ∈ segment ℝ S.triangle.v3 x := hw.mem_segment
        rw [← convexHull_pair] at hseg
        refine convexHull_mono ?_ hseg
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨by exact_mod_cast h3A, by
            simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v13_ne h.symm⟩
        · rcases hz with rfl
          exact ⟨by exact_mod_cast hxA, by
            simp only [Set.mem_singleton_iff]; exact fun h => hx_ne_v1 h⟩
      · apply hconv x (by exact_mod_cast hxA)
        have hseg : x ∈ segment ℝ S.triangle.v1 S.triangle.v3 := hw.mem_segment
        rw [← convexHull_pair] at hseg
        refine convexHull_mono ?_ hseg
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨by exact_mod_cast h1A, by
            simp only [Set.mem_singleton_iff]; exact fun h => hx_ne_v1 h.symm⟩
        · rcases hz with rfl
          exact ⟨by exact_mod_cast h3A, by
            simp only [Set.mem_singleton_iff]; exact fun h => hx_ne_v3 h.symm⟩
    have hv2v3v1_ne : signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 ≠ 0 := by
      have hv1O : ‖S.triangle.v1 - S.Packet.center‖ = S.Packet.radius :=
        S.Packet.moser_on_boundary_1
      have hv2O : ‖S.triangle.v2 - S.Packet.center‖ = S.Packet.radius :=
        S.Packet.moser_on_boundary_2
      have hv3O : ‖S.triangle.v3 - S.Packet.center‖ = S.Packet.radius :=
        S.Packet.moser_on_boundary_3
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        (by simpa [dist_eq_norm] using hv2O)
        (by simpa [dist_eq_norm] using hv3O)
        (by simpa [dist_eq_norm] using hv1O)
        S.triangle.v23_ne S.triangle.v13_ne.symm S.triangle.v12_ne.symm
    have harc : signedArea2 x S.triangle.v3 S.triangle.v1 *
        signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 < 0 :=
      lt_of_le_of_ne harc_le (mul_ne_zero hxv3v1_ne hv2v3v1_ne)
    have hflip1 : signedArea2 x S.triangle.v3 S.triangle.v1 =
        -signedArea2 x S.triangle.v1 S.triangle.v3 := by
      simp only [signedArea2]; ring
    have hflip2 : signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 =
        -signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 := by
      simp only [signedArea2]; ring
    rw [hflip1, hflip2] at harc
    nlinarith only [harc]
  have hclash : r ^ 2 * t ^ 2 <
      signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 ^ 2 :=
    b3n9m053_subshapeB_clash (by rw [dist_comm]; exact hv2v1) hv2v3 hxv1 hxv3
      (by rw [dist_comm]; exact hv2x) hnonob hAB
  have hupper : signedArea2 S.triangle.v1 S.triangle.v2 S.triangle.v3 ^ 2 ≤ r ^ 2 * t ^ 2 := by
    set v1 := S.triangle.v1 with hv1def
    set v2 := S.triangle.v2 with hv2def
    set v3 := S.triangle.v3 with hv3def
    have ha1A : a₁ ∈ A :=
      S.CP.C1_subset (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha1I1))
    have ha1C1 : a₁ ∈ S.CP.C1 :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha1I1)
    have ha1ne3 : a₁ ≠ v3 := (Finset.mem_erase.mp ha1I1).1
    have ha1ne2 : a₁ ≠ v2 :=
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase ha1I1)).1
    have hle : signedArea2 a₁ v2 v3 * signedArea2 v1 v2 v3 ≤ 0 :=
      (S.CP.arc_membership a₁ ha1A).1.mp ha1C1
    have h2A : v2 ∈ A := S.triangle.v2_mem
    have h3A : v3 ∈ A := S.triangle.v3_mem
    have ha1SAne : signedArea2 a₁ v2 v3 ≠ 0 := by
      intro hΔ
      have hcol : Collinear ℝ ({a₁, v2, v3} : Set ℝ²) :=
        Problem97.collinear_of_signedArea2_eq_zero a₁ v2 v3 hΔ
      have hconv : ConvexIndep A := S.hconv
      rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
      · apply hconv v2 (by exact_mod_cast h2A)
        have hseg : v2 ∈ segment ℝ a₁ v3 := hw.mem_segment
        rw [← convexHull_pair] at hseg
        refine convexHull_mono ?_ hseg
        intro p hp
        rcases hp with rfl | hp
        · exact ⟨by exact_mod_cast ha1A, by
            simp only [Set.mem_singleton_iff]; exact fun h => ha1ne2 h⟩
        · rcases hp with rfl
          exact ⟨by exact_mod_cast h3A, by
            simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v23_ne h.symm⟩
      · apply hconv v3 (by exact_mod_cast h3A)
        have hseg : v3 ∈ segment ℝ v2 a₁ := hw.mem_segment
        rw [← convexHull_pair] at hseg
        refine convexHull_mono ?_ hseg
        intro p hp
        rcases hp with rfl | hp
        · exact ⟨by exact_mod_cast h2A, by
            simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v23_ne h⟩
        · rcases hp with rfl
          exact ⟨by exact_mod_cast ha1A, by
            simp only [Set.mem_singleton_iff]; exact fun h => ha1ne3 h⟩
      · apply hconv a₁ (by exact_mod_cast ha1A)
        have hseg : a₁ ∈ segment ℝ v3 v2 := hw.mem_segment
        rw [← convexHull_pair] at hseg
        refine convexHull_mono ?_ hseg
        intro p hp
        rcases hp with rfl | hp
        · exact ⟨by exact_mod_cast h3A, by
            simp only [Set.mem_singleton_iff]; exact fun h => ha1ne3 h.symm⟩
        · rcases hp with rfl
          exact ⟨by exact_mod_cast h2A, by
            simp only [Set.mem_singleton_iff]; exact fun h => ha1ne2 h.symm⟩
    have hv1SAne : signedArea2 v1 v2 v3 ≠ 0 := by
      have hv1O : ‖v1 - S.Packet.center‖ = S.Packet.radius :=
        S.Packet.moser_on_boundary_1
      have hv2O : ‖v2 - S.Packet.center‖ = S.Packet.radius :=
        S.Packet.moser_on_boundary_2
      have hv3O : ‖v3 - S.Packet.center‖ = S.Packet.radius :=
        S.Packet.moser_on_boundary_3
      exact MEC.signedArea2_ne_zero_of_three_dist_eq
        (by simpa [dist_eq_norm] using hv1O)
        (by simpa [dist_eq_norm] using hv2O)
        (by simpa [dist_eq_norm] using hv3O)
        S.triangle.v12_ne S.triangle.v23_ne S.triangle.v13_ne
    have hstrict : signedArea2 a₁ v2 v3 * signedArea2 v1 v2 v3 < 0 :=
      lt_of_le_of_ne hle (mul_ne_zero ha1SAne hv1SAne)
    have hcross : signedArea2 v1 v2 v3 - signedArea2 a₁ v2 v3 =
        (v2 0 - v3 0) * (a₁ 1 - v1 1) - (v2 1 - v3 1) * (a₁ 0 - v1 0) := by
      simp only [signedArea2]; ring
    have hcs : ((v2 0 - v3 0) * (a₁ 1 - v1 1) - (v2 1 - v3 1) * (a₁ 0 - v1 0)) ^ 2
        ≤ t ^ 2 * r ^ 2 := by
      have e23 := dist_sq_coord v2 v3; have e1a1 := dist_sq_coord v1 a₁
      rw [hv2v3] at e23; rw [hv1a1] at e1a1
      nlinarith only [e23, e1a1, sq_nonneg ((v2 0 - v3 0) * (a₁ 0 - v1 0) + (v2 1 - v3 1) * (a₁ 1 - v1 1))]

    have ha1sq : 0 < signedArea2 a₁ v2 v3 ^ 2 := by positivity
    have hgap : signedArea2 v1 v2 v3 ^ 2 <
        (signedArea2 v1 v2 v3 - signedArea2 a₁ v2 v3) ^ 2 := by
      nlinarith only [hstrict, ha1sq]
    rw [hcross] at hgap
    nlinarith only [hclash, hcs, hgap]
  linarith
set_option maxHeartbeats 1600000 in
theorem b3n9m053_equilateral_rWindow
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {a₁ : ℝ²} {r t : ℝ}
    (ht : 0 < t)
    (ha1I1 : a₁ ∈ S.I1)
    (hv1a1 : dist S.triangle.v1 a₁ = r)
    (hv2v3 : dist S.triangle.v2 S.triangle.v3 = t)
    (hv2v1 : dist S.triangle.v2 S.triangle.v1 = t)
    (hv3v1 : dist S.triangle.v3 S.triangle.v1 = t) :
    3 * t ^ 2 < 4 * r ^ 2 := by
  set v1 := S.triangle.v1 with hv1def
  set v2 := S.triangle.v2 with hv2def
  set v3 := S.triangle.v3 with hv3def
  have ha1A : a₁ ∈ A :=
    S.CP.C1_subset (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha1I1))
  have ha1C1 : a₁ ∈ S.CP.C1 :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha1I1)
  have ha1ne3 : a₁ ≠ v3 := (Finset.mem_erase.mp ha1I1).1
  have ha1ne2 : a₁ ≠ v2 :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase ha1I1)).1
  have hle : signedArea2 a₁ v2 v3 * signedArea2 v1 v2 v3 ≤ 0 :=
    (S.CP.arc_membership a₁ ha1A).1.mp ha1C1
  have h2A : v2 ∈ A := S.triangle.v2_mem
  have h3A : v3 ∈ A := S.triangle.v3_mem
  have ha1SAne : signedArea2 a₁ v2 v3 ≠ 0 := by
    intro hΔ
    have hcol : Collinear ℝ ({a₁, v2, v3} : Set ℝ²) :=
      Problem97.collinear_of_signedArea2_eq_zero a₁ v2 v3 hΔ
    have hconv : ConvexIndep A := S.hconv
    rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
    · apply hconv v2 (by exact_mod_cast h2A)
      have hseg : v2 ∈ segment ℝ a₁ v3 := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro p hp
      rcases hp with rfl | hp
      · exact ⟨by exact_mod_cast ha1A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha1ne2 h⟩
      · rcases hp with rfl
        exact ⟨by exact_mod_cast h3A, by
          simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v23_ne h.symm⟩
    · apply hconv v3 (by exact_mod_cast h3A)
      have hseg : v3 ∈ segment ℝ v2 a₁ := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro p hp
      rcases hp with rfl | hp
      · exact ⟨by exact_mod_cast h2A, by
          simp only [Set.mem_singleton_iff]; exact fun h => S.triangle.v23_ne h⟩
      · rcases hp with rfl
        exact ⟨by exact_mod_cast ha1A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha1ne3 h⟩
    · apply hconv a₁ (by exact_mod_cast ha1A)
      have hseg : a₁ ∈ segment ℝ v3 v2 := hw.mem_segment
      rw [← convexHull_pair] at hseg
      refine convexHull_mono ?_ hseg
      intro p hp
      rcases hp with rfl | hp
      · exact ⟨by exact_mod_cast h3A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha1ne3 h.symm⟩
      · rcases hp with rfl
        exact ⟨by exact_mod_cast h2A, by
          simp only [Set.mem_singleton_iff]; exact fun h => ha1ne2 h.symm⟩
  have harea : 4 * signedArea2 v1 v2 v3 ^ 2 = 3 * t ^ 4 := by
    have e12 := dist_sq_coord v1 v2; have e23 := dist_sq_coord v2 v3
    have e31 := dist_sq_coord v3 v1
    rw [show dist v1 v2 = t by rw [dist_comm]; exact hv2v1] at e12
    rw [hv2v3] at e23
    rw [hv3v1] at e31
    simp only [signedArea2]; nlinarith only [e12, e23, e31]
  have hv1SAne : signedArea2 v1 v2 v3 ≠ 0 := by
    intro hz; rw [hz] at harea; nlinarith only [harea, ht, pow_pos ht 4]
  have hstrict : signedArea2 a₁ v2 v3 * signedArea2 v1 v2 v3 < 0 :=
    lt_of_le_of_ne hle (mul_ne_zero ha1SAne hv1SAne)
  have hcross : signedArea2 v1 v2 v3 - signedArea2 a₁ v2 v3 =
      (v2 0 - v3 0) * (a₁ 1 - v1 1) - (v2 1 - v3 1) * (a₁ 0 - v1 0) := by
    simp only [signedArea2]; ring
  have hcs : ((v2 0 - v3 0) * (a₁ 1 - v1 1) - (v2 1 - v3 1) * (a₁ 0 - v1 0)) ^ 2
      ≤ t ^ 2 * r ^ 2 := by
    have e23 := dist_sq_coord v2 v3; have e1a1 := dist_sq_coord v1 a₁
    rw [hv2v3] at e23; rw [hv1a1] at e1a1
    nlinarith only [e23, e1a1, sq_nonneg ((v2 0 - v3 0) * (a₁ 0 - v1 0) + (v2 1 - v3 1) * (a₁ 1 - v1 1))]

  have ha1sq : 0 < signedArea2 a₁ v2 v3 ^ 2 := by positivity
  have hgap : signedArea2 v1 v2 v3 ^ 2 <
      (signedArea2 v1 v2 v3 - signedArea2 a₁ v2 v3) ^ 2 := by
    nlinarith only [hstrict, ha1sq]
  rw [hcross] at hgap
  nlinarith only [harea, hcs, hgap, ht, sq_nonneg t, mul_pos ht ht]
set_option maxHeartbeats 1600000 in
theorem b3n9m053_metric_pin_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {x : ℝ²} {r t ρ : ℝ}
    (ht : 0 < t) (hr : 0 < r)
    (hv2v3 : dist S.triangle.v2 S.triangle.v3 = t)
    (hv2v1 : dist S.triangle.v2 S.triangle.v1 = t)
    (hv3v1 : dist S.triangle.v3 S.triangle.v1 = t)
    (hv2x : dist S.triangle.v2 x = t)
    (hv1x : dist S.triangle.v1 x = r)
    (hxv3 : dist x S.triangle.v3 = ρ)
    (hrwin : 3 * t ^ 2 < 4 * r ^ 2)
    (hu_lt : r ^ 2 < t ^ 2)
    (horient : 0 < signedArea2 x S.triangle.v1 S.triangle.v2 *
                 signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2) :
    4 * ρ ^ 2 < t ^ 2 := by
  set v1 := S.triangle.v1 with hv1def
  set v2 := S.triangle.v2 with hv2def
  set v3 := S.triangle.v3 with hv3def
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hkey : 3 * (t ^ 2 - r ^ 2 / 2) ^ 2 + (t ^ 2 + r ^ 2 / 2 - ρ ^ 2) ^ 2 = 3 * t ^ 4
      ∧ 0 < t ^ 2 + r ^ 2 / 2 - ρ ^ 2 := by
    obtain ⟨a0, a1, b0, b1, c0, c1, ha0, ha1, hb0, hb1, hc0, hc1⟩ :
        ∃ a0 a1 b0 b1 c0 c1 : ℝ, a0 = x 0 - v2 0 ∧ a1 = x 1 - v2 1 ∧
          b0 = v1 0 - v2 0 ∧ b1 = v1 1 - v2 1 ∧ c0 = v3 0 - v2 0 ∧ c1 = v3 1 - v2 1 :=
      ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have e_v2v3 := dist_sq_coord v2 v3; rw [hv2v3] at e_v2v3
    have e_v2v1 := dist_sq_coord v2 v1; rw [hv2v1] at e_v2v1
    have e_v3v1 := dist_sq_coord v3 v1; rw [hv3v1] at e_v3v1
    have e_v2x := dist_sq_coord v2 x; rw [hv2x] at e_v2x
    have e_v1x := dist_sq_coord v1 x; rw [hv1x] at e_v1x
    have e_xv3 := dist_sq_coord x v3; rw [hxv3] at e_xv3
    have gAA : a0 ^ 2 + a1 ^ 2 = t ^ 2 := by rw [ha0, ha1]; linear_combination -e_v2x
    have gBB : b0 ^ 2 + b1 ^ 2 = t ^ 2 := by rw [hb0, hb1]; linear_combination -e_v2v1
    have gCC : c0 ^ 2 + c1 ^ 2 = t ^ 2 := by rw [hc0, hc1]; linear_combination -e_v2v3
    have gAB : a0 * b0 + a1 * b1 = t ^ 2 - r ^ 2 / 2 := by
      rw [ha0, ha1, hb0, hb1]; linear_combination (-e_v2x) / 2 + (-e_v2v1) / 2 + e_v1x / 2
    have gAC : a0 * c0 + a1 * c1 = t ^ 2 - ρ ^ 2 / 2 := by
      rw [ha0, ha1, hc0, hc1]; linear_combination (-e_v2x) / 2 + (-e_v2v3) / 2 + e_xv3 / 2
    have gBC : b0 * c0 + b1 * c1 = t ^ 2 / 2 := by
      rw [hb0, hb1, hc0, hc1]; linear_combination (-e_v2v1) / 2 + (-e_v2v3) / 2 + e_v3v1 / 2
    have hsaX : signedArea2 x v1 v2 = a0 * b1 - a1 * b0 := by
      rw [ha0, ha1, hb0, hb1]; simp only [signedArea2]; ring
    have hsaV : signedArea2 v3 v1 v2 = -b0 * c1 + b1 * c0 := by
      rw [hb0, hb1, hc0, hc1]; simp only [signedArea2]; ring
    rw [hsaX, hsaV] at horient
    clear ha0 ha1 hb0 hb1 hc0 hc1 e_v2v3 e_v2v1 e_v3v1 e_v2x e_v1x e_xv3
      hsaX hsaV hv2v3 hv2v1 hv3v1 hv2x hv1x hxv3 hr hrwin hu_lt ht
      hv1def hv2def hv3def
    refine ⟨?_, ?_⟩
    ·
      have hgram :
          (a0 ^ 2 + a1 ^ 2)
              * ((b0 ^ 2 + b1 ^ 2) * (c0 ^ 2 + c1 ^ 2)
                  - (b0 * c0 + b1 * c1) * (b0 * c0 + b1 * c1))
            - (a0 * b0 + a1 * b1)
              * ((a0 * b0 + a1 * b1) * (c0 ^ 2 + c1 ^ 2)
                  - (b0 * c0 + b1 * c1) * (a0 * c0 + a1 * c1))
            + (a0 * c0 + a1 * c1)
              * ((a0 * b0 + a1 * b1) * (b0 * c0 + b1 * c1)
                  - (b0 ^ 2 + b1 ^ 2) * (a0 * c0 + a1 * c1)) = 0 := by
        ring
      rw [gAA, gBB, gCC, gAB, gAC, gBC] at hgram
      nlinarith only [hgram, ht2]
    ·
      have hbid : t ^ 2 * (t ^ 2 + r ^ 2 / 2 - ρ ^ 2)
          = 2 * ((a0 * b1 - a1 * b0) * (-b0 * c1 + b1 * c0)) := by
        linear_combination
          (2 * a0 * c0 + 2 * a1 * c1 - 2 * b0 * c0 - 2 * b1 * c1 + ρ ^ 2 - t ^ 2) * gAA
            + (-2 * a0 * c0 - 2 * a1 * c1) * gBB
            + (2 * b0 * c0 + 2 * b1 * c1) * gAB
            + (-2 * a0 ^ 2 - 2 * a1 ^ 2) * gAC
            + (2 * a0 ^ 2 + 2 * a1 ^ 2 - r ^ 2) * gBC
      have hpos : 0 < t ^ 2 * (t ^ 2 + r ^ 2 / 2 - ρ ^ 2) := by rw [hbid]; linarith [horient]
      by_contra hc; push_neg at hc
      nlinarith only [horient, hbid, ht2, hc, mul_nonpos_of_nonneg_of_nonpos ht2.le hc, hpos]
  obtain ⟨hcon, hbranch⟩ := hkey
  nlinarith only [hcon, ht2, hrwin, hu_lt, hbranch, ht, mul_pos ht2 ht2, sq_nonneg (t ^ 2 + r ^ 2 / 2 - ρ ^ 2), sq_nonneg (4 * r ^ 2 - 3 * t ^ 2), sq_nonneg (t ^ 2 - r ^ 2), mul_pos hbranch hbranch]


set_option maxHeartbeats 1600000 in
theorem b3n9m053_hu_lt_equilateral_I2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    {x : ℝ²} {r t : ℝ}
    (ht : 0 < t)
    (hv2v3 : dist S.triangle.v2 S.triangle.v3 = t)
    (hv2v1 : dist S.triangle.v2 S.triangle.v1 = t)
    (hv3v1 : dist S.triangle.v3 S.triangle.v1 = t)
    (hv2x : dist S.triangle.v2 x = t)
    (hv1x : dist S.triangle.v1 x = r)
    (hx_ne_v3 : x ≠ S.triangle.v3)
    (harc : signedArea2 x S.triangle.v3 S.triangle.v1 *
            signedArea2 S.triangle.v2 S.triangle.v3 S.triangle.v1 ≤ 0) :
    r ^ 2 < t ^ 2 := by
  set v1 := S.triangle.v1 with hv1def
  set v2 := S.triangle.v2 with hv2def
  set v3 := S.triangle.v3 with hv3def
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  set rho : ℝ := dist x v3 with hrhodef
  have hrho2pos : 0 < rho ^ 2 := by
    have : 0 < rho := by rw [hrhodef]; exact dist_pos.mpr hx_ne_v3
    positivity
  obtain ⟨a0, a1, b0, b1, c0, c1, ha0, ha1, hb0, hb1, hc0, hc1⟩ :
      ∃ a0 a1 b0 b1 c0 c1 : ℝ, a0 = x 0 - v2 0 ∧ a1 = x 1 - v2 1 ∧
        b0 = v1 0 - v2 0 ∧ b1 = v1 1 - v2 1 ∧ c0 = v3 0 - v2 0 ∧ c1 = v3 1 - v2 1 :=
    ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have e_v2v3 := dist_sq_coord v2 v3; rw [hv2v3] at e_v2v3
  have e_v2v1 := dist_sq_coord v2 v1; rw [hv2v1] at e_v2v1
  have e_v3v1 := dist_sq_coord v3 v1; rw [hv3v1] at e_v3v1
  have e_v2x := dist_sq_coord v2 x; rw [hv2x] at e_v2x
  have e_v1x := dist_sq_coord v1 x; rw [hv1x] at e_v1x
  have e_xv3 := dist_sq_coord x v3
  have gAA : a0 ^ 2 + a1 ^ 2 = t ^ 2 := by rw [ha0, ha1]; linear_combination -e_v2x
  have gBB : b0 ^ 2 + b1 ^ 2 = t ^ 2 := by rw [hb0, hb1]; linear_combination -e_v2v1
  have gCC : c0 ^ 2 + c1 ^ 2 = t ^ 2 := by rw [hc0, hc1]; linear_combination -e_v2v3
  have gAB : a0 * b0 + a1 * b1 = t ^ 2 - r ^ 2 / 2 := by
    rw [ha0, ha1, hb0, hb1]; linear_combination (-e_v2x) / 2 + (-e_v2v1) / 2 + e_v1x / 2
  have gBC : b0 * c0 + b1 * c1 = t ^ 2 / 2 := by
    rw [hb0, hb1, hc0, hc1]; linear_combination (-e_v2v1) / 2 + (-e_v2v3) / 2 + e_v3v1 / 2
  have hrho2c : rho ^ 2 = (a0 - c0) ^ 2 + (a1 - c1) ^ 2 := by
    rw [hrhodef, e_xv3, ha0, ha1, hc0, hc1]; ring
  have hsaX : signedArea2 x v3 v1 = (c0 - a0) * (b1 - a1) - (b0 - a0) * (c1 - a1) := by
    rw [ha0, ha1, hb0, hb1, hc0, hc1]; simp only [signedArea2]; ring
  have hsaV : signedArea2 v2 v3 v1 = c0 * b1 - b0 * c1 := by
    rw [hb0, hb1, hc0, hc1]; simp only [signedArea2]; try ring
  rw [hsaX, hsaV] at harc
  clear ha0 ha1 hb0 hb1 hc0 hc1 e_v2v3 e_v2v1 e_v3v1 e_v2x e_v1x e_xv3
    hsaX hsaV hv1def hv2def hv3def hrhodef hv2v3 hv2v1 hv3v1 hv2x hv1x hx_ne_v3
  have hid : t ^ 2 * (t ^ 2 - r ^ 2)
      = -4 * (((c0 - a0) * (b1 - a1) - (b0 - a0) * (c1 - a1)) * (c0 * b1 - b0 * c1))
        + t ^ 2 * rho ^ 2 := by
    rw [hrho2c]
    linear_combination (-t ^ 2) * gAA
      + (-4 * a0 * c0 - 4 * a1 * c1 + 4 * c0 ^ 2 + 4 * c1 ^ 2) * gBB
      + (-4 * a0 * b0 - 4 * a1 * b1 + 3 * t ^ 2) * gCC
      + (4 * a0 * b0 + 4 * a0 * c0 + 4 * a1 * b1 + 4 * a1 * c1
          - 4 * b0 * c0 - 4 * b1 * c1 - 2 * t ^ 2) * gBC
      + (-2 * t ^ 2) * gAB
  nlinarith only [harc, hid, ht2, hrho2pos]
set_option maxHeartbeats 4000000 in
theorem b3n9m053_layer4_subshapeA_kill
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S)
    {x y a₁ b₁ a₃ b₃ : ℝ²} {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t)
    (hxI2 : x ∈ S.I2) (hyI3 : y ∈ S.I3) (ha3I3 : a₃ ∈ S.I3) (hb3I3 : b₃ ∈ S.I3)
    (hI1eq : S.I1 = ({a₁, b₁} : Finset ℝ²)) (hI3eq : S.I3 = ({a₃, b₃} : Finset ℝ²))
    (hxA : x ∈ A)
    (ha1I1 : a₁ ∈ S.I1) (hv1a1 : dist S.triangle.v1 a₁ = r)
    (hb1I1 : b₁ ∈ S.I1) (hv1b1 : dist S.triangle.v1 b₁ = r)
    (hv1x : dist S.triangle.v1 x = r) (hv1y : dist S.triangle.v1 y = r)
    (hv2x : dist S.triangle.v2 x = t) (hv3y : dist S.triangle.v3 y = t)
    (hv3a3 : dist S.triangle.v3 a₃ = t) (hv3b3 : dist S.triangle.v3 b₃ = t)
    (hv2v3 : dist S.triangle.v2 S.triangle.v3 = t)
    (hv2v1 : dist S.triangle.v2 S.triangle.v1 = t)
    (hv3v1 : dist S.triangle.v3 S.triangle.v1 = t)
    (horient : 0 < signedArea2 x S.triangle.v1 S.triangle.v2 *
                 signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2) :
    False := by
  classical
  obtain ⟨ρ, hρpos, hKcard⟩ := S.hK4 x hxA
  set K : Finset ℝ² := A.filter (fun q => dist x q = ρ) with hKdef
  have hKcard' : 4 ≤ K.card := hKcard
  set v1 := S.triangle.v1 with hv1def
  set v2 := S.triangle.v2 with hv2def
  set v3 := S.triangle.v3 with hv3def
  have hxI2' : x ∈ ({Z.a2, Z.b2} : Finset ℝ²) := by rw [← Z.hI2]; exact hxI2
  have ha2b2 : Z.a2 ≠ Z.b2 := by
    have h2 : ({Z.a2, Z.b2} : Finset ℝ²).card = 2 := by rw [← Z.hI2]; exact (p2mCoreSupport S).I2_card_eq_two
    by_contra h; rw [h] at h2; simp at h2
  obtain ⟨zstar, hzI2, hxz⟩ :
      ∃ zstar, zstar ∈ S.I2 ∧ x ≠ zstar := by
    rcases Finset.mem_insert.mp hxI2' with hxa2 | hxb2
    · exact ⟨Z.b2, by rw [Z.hI2]; simp, by rw [hxa2]; exact ha2b2⟩
    · have hxb2' : x = Z.b2 := by simpa using hxb2
      exact ⟨Z.a2, by rw [Z.hI2]; simp, by rw [hxb2']; exact (Ne.symm ha2b2)⟩
  have hL1 : 0 < signedArea2 v1 v3 x * signedArea2 v2 v3 x :=
    b3n9m053_v1_same_side_of_v3x_chord S hxI2
  have hSAv2ne : signedArea2 v2 v3 x ≠ 0 := by
    intro h; rw [h, mul_zero] at hL1; exact (lt_irrefl 0) hL1
  have hcertA3 : 0 < signedArea2 a₃ v3 x * signedArea2 v2 v3 x :=
    b3n9m053_c3_same_side_of_v3x_chord S ha3I3 hxI2 hv2v3 hv2x ht
  have hcertB3 : 0 < signedArea2 b₃ v3 x * signedArea2 v2 v3 x :=
    b3n9m053_c3_same_side_of_v3x_chord S hb3I3 hxI2 hv2v3 hv2x ht
  have hcertA1 : 0 < signedArea2 a₁ v1 x * signedArea2 v3 v1 x :=
    b3n9m053_c1_same_side_of_v1x_chord S ha1I1 hxI2
  have hcertB1 : 0 < signedArea2 b₁ v1 x * signedArea2 v3 v1 x :=
    b3n9m053_c1_same_side_of_v1x_chord S hb1I1 hxI2
  have hxnotK : x ∉ K := by
    rw [hKdef, Finset.mem_filter]; rintro ⟨-, hd⟩
    rw [dist_self] at hd; exact (ne_of_lt hρpos) hd
  set P1 : Finset ℝ² := {v1, v2, a₃, b₃} with hP1def
  set P2 : Finset ℝ² := {a₁, b₁} with hP2def
  set T : Finset ℝ² := {v3, zstar} with hTdef
  have hsieveP1 : (P1.filter (fun p => dist p x = ρ)).card ≤ 1 := by
    apply b3n9m053_sieve_at_most_one_on_xcircle (c := v3) (τ := t)
      (σ := signedArea2 v2 v3 x)
    · intro p hp
      rw [hP1def] at hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl|rfl|rfl|rfl
      · rw [dist_comm]; exact hv3v1
      · exact hv2v3
      · rw [dist_comm]; exact hv3a3
      · rw [dist_comm]; exact hv3b3
    · intro p hp
      rw [hP1def] at hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl|rfl|rfl|rfl
      · exact hL1
      · exact mul_self_pos.mpr hSAv2ne
      · exact hcertA3
      · exact hcertB3
  have hsieveP2 : (P2.filter (fun p => dist p x = ρ)).card ≤ 1 := by
    apply b3n9m053_sieve_at_most_one_on_xcircle (c := v1) (τ := r)
      (σ := signedArea2 v3 v1 x)
    · intro p hp
      rw [hP2def] at hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl|rfl
      · rw [dist_comm]; exact hv1a1
      · rw [dist_comm]; exact hv1b1
    · intro p hp
      rw [hP2def] at hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl|rfl
      · exact hcertA1
      · exact hcertB1
  have hKP1 : (K ∩ P1).card ≤ 1 := by
    refine le_trans (Finset.card_le_card ?_) hsieveP1
    intro q hq; rcases Finset.mem_inter.mp hq with ⟨hqK, hqP1⟩
    rw [Finset.mem_filter]; refine ⟨hqP1, ?_⟩
    have hd : dist x q = ρ := by rw [hKdef, Finset.mem_filter] at hqK; exact hqK.2
    rw [dist_comm]; exact hd
  have hKP2 : (K ∩ P2).card ≤ 1 := by
    refine le_trans (Finset.card_le_card ?_) hsieveP2
    intro q hq; rcases Finset.mem_inter.mp hq with ⟨hqK, hqP2⟩
    rw [Finset.mem_filter]; refine ⟨hqP2, ?_⟩
    have hd : dist x q = ρ := by rw [hKdef, Finset.mem_filter] at hqK; exact hqK.2
    rw [dist_comm]; exact hd
  have hAcover : A ⊆ ({v1, v2, v3} : Finset ℝ²) ∪ S.I1 ∪ S.I2 ∪ S.I3 := by
    intro p hpA
    by_cases hpv1 : p = v1
    · subst hpv1; simp
    by_cases hpv2 : p = v2
    · subst hpv2; simp
    by_cases hpv3 : p = v3
    · subst hpv3; simp
    have hnm : p ∉ S.triangle.verts := by
      simp only [Problem97.MoserTriangle.verts, Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hpv1, hpv2, hpv3⟩
    have hone := S.CP.nonmoser_in_one p hpA hnm
    by_cases hC1 : p ∈ S.CP.C1
    · have hpI1 : p ∈ S.I1 := by
        rw [show S.I1 = (S.CP.C1.erase v2).erase v3 from rfl]
        rw [Finset.mem_erase, Finset.mem_erase]; exact ⟨hpv3, hpv2, hC1⟩
      simp [hpI1]
    by_cases hC2 : p ∈ S.CP.C2
    · have hpI2 : p ∈ S.I2 := by
        rw [show S.I2 = (S.CP.C2.erase v3).erase v1 from rfl]
        rw [Finset.mem_erase, Finset.mem_erase]; exact ⟨hpv1, hpv3, hC2⟩
      simp [hpI2]
    by_cases hC3 : p ∈ S.CP.C3
    · have hpI3 : p ∈ S.I3 := by
        rw [show S.I3 = (S.CP.C3.erase v1).erase v2 from rfl]
        rw [Finset.mem_erase, Finset.mem_erase]; exact ⟨hpv2, hpv1, hC3⟩
      simp [hpI3]
    · exfalso; simp only [hC1, hC2, hC3, if_false] at hone; simp at hone
  have hI2eq : S.I2 = ({x, zstar} : Finset ℝ²) := by
    have hcard : S.I2.card = 2 := (p2mCoreSupport S).I2_card_eq_two
    have hsub : ({x, zstar} : Finset ℝ²) ⊆ S.I2 := by
      intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> assumption
    have hcard2 : ({x, zstar} : Finset ℝ²).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hxz]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard2])).symm
  have hcover : ∀ q ∈ A, q ≠ v3 → q ≠ zstar → q ≠ x → q ∈ P1 ∨ q ∈ P2 := by
    intro q hqA hqv3 hqz hqx
    have hq9 := hAcover hqA
    rcases Finset.mem_union.mp hq9 with hq789 | hI3mem
    · rcases Finset.mem_union.mp hq789 with hq456 | hI2mem
      · rcases Finset.mem_union.mp hq456 with hverts | hI1mem
        ·
          simp only [Finset.mem_insert, Finset.mem_singleton] at hverts
          rcases hverts with hqv1 | hqv2 | hqv3'
          · exact Or.inl (by rw [hP1def]; simp [hqv1])
          · exact Or.inl (by rw [hP1def]; simp [hqv2])
          · exact absurd hqv3' hqv3
        ·
          right; exact hI1eq ▸ hI1mem
      ·
        rw [hI2eq] at hI2mem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hI2mem
        rcases hI2mem with hxc | hzc
        · exact absurd hxc hqx
        · exact absurd hzc hqz
    ·
      left; rw [hP1def]; rw [hI3eq] at hI3mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hI3mem ⊢
      tauto
  have hKsub : K ⊆ A := by rw [hKdef]; exact Finset.filter_subset _ _
  have hsubT : K \ T ⊆ (K ∩ P1) ∪ (K ∩ P2) := by
    intro q hq; rcases Finset.mem_sdiff.mp hq with ⟨hqK, hqT⟩
    have hqA : q ∈ A := hKsub hqK
    have hqv3 : q ≠ v3 := by intro h; exact hqT (by rw [hTdef, h]; simp)
    have hqz : q ≠ zstar := by intro h; exact hqT (by rw [hTdef, h]; simp)
    have hqx : q ≠ x := by intro h; exact hxnotK (h ▸ hqK)
    rcases hcover q hqA hqv3 hqz hqx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hqK, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hqK, h⟩)
  have hsplit : (K \ T).card + (K ∩ T).card = K.card :=
    Finset.card_sdiff_add_card_inter K T
  by_cases hv3K : v3 ∈ K
  ·
    have hxv3 : dist x v3 = ρ := by
      rw [hKdef, Finset.mem_filter] at hv3K; exact hv3K.2
    have hx_ne_v3 : x ≠ v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1
    have harc_le : signedArea2 x v3 v1 * signedArea2 v2 v3 v1 ≤ 0 := by
      have haC2 : x ∈ S.CP.C2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).2
      exact ((S.CP.arc_membership x hxA).2.1).mp haC2
    have hu_lt : r ^ 2 < t ^ 2 :=
      b3n9m053_hu_lt_equilateral_I2 S ht hv2v3 hv2v1 hv3v1 hv2x hv1x hx_ne_v3 harc_le
    have hrwin : 3 * t ^ 2 < 4 * r ^ 2 :=
      S.b3n9m053_equilateral_rWindow ht ha1I1 hv1a1 hv2v3 hv2v1 hv3v1
    have hpin : 4 * ρ ^ 2 < t ^ 2 :=
      b3n9m053_metric_pin_v3 S ht hr hv2v3 hv2v1 hv3v1 hv2x hv1x hxv3 hrwin hu_lt horient
    have hρnn : 0 ≤ ρ := le_of_lt hρpos
    have ht2ρ : 2 * ρ < t := by nlinarith only [ht, hpin, hρnn, sq_nonneg (t - 2 * ρ)]
    have hP1notK : ∀ p ∈ P1, p ∉ K := by
      intro p hp hpK
      have hpdist : dist x p = ρ := by
        rw [hKdef, Finset.mem_filter] at hpK; exact hpK.2
      have hv3p : dist v3 p = t := by
        rw [hP1def] at hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact hv3v1
        · rw [dist_comm]; exact hv2v3
        · exact hv3a3
        · exact hv3b3
      have htri : dist v3 p ≤ dist v3 x + dist x p := dist_triangle v3 x p
      rw [hv3p, dist_comm v3 x, hxv3, hpdist] at htri
      linarith [ht2ρ]
    have hKP1zero : (K ∩ P1).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro q hq; rcases Finset.mem_inter.mp hq with ⟨hqK, hqP1⟩
      exact hP1notK q hqP1 hqK
    have hKsdiff : (K \ T).card ≤ 1 := by
      calc (K \ T).card ≤ ((K ∩ P1) ∪ (K ∩ P2)).card := Finset.card_le_card hsubT
        _ ≤ (K ∩ P1).card + (K ∩ P2).card := Finset.card_union_le _ _
        _ ≤ 1 := by omega
    have hTcard : T.card ≤ 2 := by
      rw [hTdef]; exact le_trans (Finset.card_insert_le _ _) (by simp)
    have hKTle : (K ∩ T).card ≤ 2 :=
      le_trans (Finset.card_le_card Finset.inter_subset_right) hTcard
    omega
  ·
    have hKsdiff : (K \ T).card ≤ 2 := by
      calc (K \ T).card ≤ ((K ∩ P1) ∪ (K ∩ P2)).card := Finset.card_le_card hsubT
        _ ≤ (K ∩ P1).card + (K ∩ P2).card := Finset.card_union_le _ _
        _ ≤ 2 := by omega
    have hKTsub : K ∩ T ⊆ ({zstar} : Finset ℝ²) := by
      intro q hq; rcases Finset.mem_inter.mp hq with ⟨hqK, hqT⟩
      rw [hTdef] at hqT; simp only [Finset.mem_insert, Finset.mem_singleton] at hqT
      rcases hqT with hqv3 | hqz
      · exact absurd (hqv3 ▸ hqK) hv3K
      · simp [hqz]
    have hKTle : (K ∩ T).card ≤ 1 :=
      le_trans (Finset.card_le_card hKTsub) (by simp)
    omega
theorem formA_v1_endpointPair_impossible
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hr : 0 < r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hA : S.IsFormA_v1 r)
    (hT2card : (S.witnessClassAt_v2 s).card = 4)
    (hI2sub : S.I2 ⊆ S.witnessClassAt_v2 s)
    (hpv3 : S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²))
    (hqv1 : S.witnessClassAt_v2 s ∩ S.CP.C3 = ({S.triangle.v1} : Finset ℝ²)) :
    False := by
  classical
  have hv3T2 : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
    have hmem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    rw [← hpv3] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hv1T2 : S.triangle.v1 ∈ S.witnessClassAt_v2 s := by
    have hmem : S.triangle.v1 ∈ ({S.triangle.v1} : Finset ℝ²) := by simp
    rw [← hqv1] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hv2v3 : dist S.triangle.v2 S.triangle.v3 = s := (Finset.mem_filter.mp hv3T2).2
  have hv2v1 : dist S.triangle.v2 S.triangle.v1 = s := (Finset.mem_filter.mp hv1T2).2
  have hs_pos : 0 < s := by
    rw [← hv2v3]; exact dist_pos.mpr S.triangle.v23_ne
  obtain ⟨x, y, hxI2, hyI3, hxeq, hyeq⟩ := hA
  have hxT1 : x ∈ S.witnessClassAt_v1 r := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).1
  have hyT1 : y ∈ S.witnessClassAt_v1 r := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).1
  have hv1x : dist S.triangle.v1 x = r := (Finset.mem_filter.mp hxT1).2
  have hv1y : dist S.triangle.v1 y = r := (Finset.mem_filter.mp hyT1).2
  have hxA : x ∈ A :=
    S.CP.C2_subset (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).2
  have hxT2 : x ∈ S.witnessClassAt_v2 s := hI2sub hxI2
  have hv2x : dist S.triangle.v2 x = s := (Finset.mem_filter.mp hxT2).2
  have hcore1 := (p2mCoreSupport S).coreSelector_v1 hr hcard
  rcases hcore1 with ⟨-, hI1sub1, -, -⟩
  rcases p2mSelectorShape_v3 S Z with ⟨t, ht, hshape3⟩
  simp only [] at hshape3
  obtain ⟨hTcard3, hI3sub3, p3, q3, hp3named, hq3named, hp3C1, hq3C2⟩ := hshape3
  have ha3I3 : Z.a3 ∈ S.I3 := by rw [Z.hI3]; simp
  have hb3I3 : Z.b3 ∈ S.I3 := by rw [Z.hI3]; simp
  have hp3T3 : p3 ∈ S.witnessClassAt_v3 t := by
    have hmem : p3 ∈ ({p3} : Finset ℝ²) := by simp
    rw [← hp3C1] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hq3T3 : q3 ∈ S.witnessClassAt_v3 t := by
    have hmem : q3 ∈ ({q3} : Finset ℝ²) := by simp
    rw [← hq3C2] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hv3p3 : dist S.triangle.v3 p3 = t := (Finset.mem_filter.mp hp3T3).2
  have hv3q3 : dist S.triangle.v3 q3 = t := (Finset.mem_filter.mp hq3T3).2
  have hp3_not_I1 :
      ¬ p3 ∈ S.I1 := by
    intro hp3I1
    have hp3T1 : p3 ∈ S.witnessClassAt_v1 r := hI1sub1 hp3I1
    have hyT3 : y ∈ S.witnessClassAt_v3 t := hI3sub3 hyI3
    have hv1p3 : dist S.triangle.v1 p3 = r := (Finset.mem_filter.mp hp3T1).2
    have hv3y : dist S.triangle.v3 y = t := (Finset.mem_filter.mp hyT3).2
    have hp3C1 : p3 ∈ S.CP.C1 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hp3I1).2).2
    have hyC3 : y ∈ S.CP.C3 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hyI3).2).2
    have hy_not_C1 : y ∉ S.CP.C1 := by
      intro hyC1
      have hyA : y ∈ A := S.CP.C3_subset hyC3
      have hy_ne_v2 : y ≠ S.triangle.v2 := (Finset.mem_erase.mp hyI3).1
      have hy_ne_v1 : y ≠ S.triangle.v1 :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hyI3).2).1
      have hy_ne_v3 : y ≠ S.triangle.v3 := by
        intro h
        exact S.CP.v3_notin_C3 (by simpa [h] using hyC3)
      have hynonmoser : y ∉ S.triangle.verts := by
        simp [Problem97.MoserTriangle.verts, hy_ne_v1, hy_ne_v2, hy_ne_v3]
      have hone := S.CP.nonmoser_in_one y hyA hynonmoser
      by_cases hyC2 : y ∈ S.CP.C2
      · have : (3 : ℕ) = 1 := by
          simpa [hyC1, hyC2, hyC3] using hone
        omega
      · have : (2 : ℕ) = 1 := by
          simpa [hyC1, hyC2, hyC3] using hone
        omega
    have hyp3 : y ≠ p3 := by
      intro h
      exact hy_not_C1 (by simpa [h] using hp3C1)
    have hmid :
        signedArea2 (midpoint ℝ y p3) S.triangle.v1 S.triangle.v3 = 0 :=
      twoCircle_midpoint_collinear
        (by simpa [dist_comm] using hv1p3)
        (by simpa [dist_comm] using hv1y)
        (by simpa [dist_comm] using hv3p3)
        (by simpa [dist_comm] using hv3y)
        hyp3.symm
    have hreflect :
        signedArea2 p3 S.triangle.v1 S.triangle.v3 =
          -signedArea2 y S.triangle.v1 S.triangle.v3 :=
      signedArea2_reflection_neg
        (q := S.triangle.v1) (v2 := S.triangle.v3) (y := y) (u := p3) hmid
    have hy_side :
        0 < signedArea2 y S.triangle.v1 S.triangle.v3 *
          signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 :=
      b3n9m053_c3_vertex_same_open_side_as_v2' S hyI3
    have hp_side :
        0 < signedArea2 p3 S.triangle.v1 S.triangle.v3 *
          signedArea2 S.triangle.v2 S.triangle.v1 S.triangle.v3 :=
      b3n9m053_c1_vertex_same_open_side_as_v2' S hp3I1
    rw [hreflect] at hp_side
    linarith
  have hp3v2 : p3 = S.triangle.v2 := by
    rcases Finset.mem_insert.mp hp3named with hp3a1 | hp3rest
    · exfalso
      apply hp3_not_I1
      rw [hp3a1, Z.hI1]
      simp
    rcases Finset.mem_insert.mp hp3rest with hp3b1 | hp3v2
    · exfalso
      apply hp3_not_I1
      rw [hp3b1, Z.hI1]
      simp
    · simpa using hp3v2
  have hts : t = s := by
    have : dist S.triangle.v3 S.triangle.v2 = t := by rw [← hp3v2]; exact hv3p3
    rw [← this]; rw [dist_comm]; exact hv2v3
  subst hts
  have hv3y : dist S.triangle.v3 y = t := (Finset.mem_filter.mp (hI3sub3 hyI3)).2
  have hv3a3 : dist S.triangle.v3 Z.a3 = t := (Finset.mem_filter.mp (hI3sub3 ha3I3)).2
  have hv3b3 : dist S.triangle.v3 Z.b3 = t := (Finset.mem_filter.mp (hI3sub3 hb3I3)).2
  have hZa1I1 : Z.a1 ∈ S.I1 := by rw [Z.hI1]; simp
  have hv1Za1 : dist S.triangle.v1 Z.a1 = r :=
    (Finset.mem_filter.mp (hI1sub1 hZa1I1)).2
  have hZb1I1 : Z.b1 ∈ S.I1 := by rw [Z.hI1]; simp
  have hv1Zb1 : dist S.triangle.v1 Z.b1 = r :=
    (Finset.mem_filter.mp (hI1sub1 hZb1I1)).2
  have hxorient : 0 < signedArea2 x S.triangle.v1 S.triangle.v2 *
      signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 :=
    (p2mCoreSupport S).c2_vertex_same_open_side_as_v3 hxI2
  have hq3I2_kill : q3 ∈ S.I2 → False := by
    intro hq3I2
    have hv2q3 : dist S.triangle.v2 q3 = t := (Finset.mem_filter.mp (hI2sub hq3I2)).2
    exact b3n9m053_layer4_subshapeB_kill S Z hr ht hxI2 hyI3 ha3I3 hb3I3 Z.hI1 Z.hI3 hxA
      hZa1I1 hv1Za1 hZb1I1 hv1Zb1 hv1x hv1y hv2x hv3y hv3a3 hv3b3
      hv2v3 hv2v1 hv2q3 hv3q3 hq3I2 hxorient
  rcases Finset.mem_insert.mp hq3named with hq3a2 | hq3rest
  · exact hq3I2_kill (by rw [hq3a2, Z.hI2]; simp)
  rcases Finset.mem_insert.mp hq3rest with hq3b2 | hq3v1
  · refine hq3I2_kill ?_
    have hq3b2' : q3 = Z.b2 := by simpa using hq3b2
    rw [hq3b2', Z.hI2]; simp
  ·
    have hq3v1' : q3 = S.triangle.v1 := by simpa using hq3v1
    have hv3v1 : dist S.triangle.v3 S.triangle.v1 = t := by rw [← hq3v1']; exact hv3q3
    exact b3n9m053_layer4_subshapeA_kill S Z hr ht hxI2 hyI3 ha3I3 hb3I3 Z.hI1 Z.hI3 hxA
      hZa1I1 hv1Za1 hZb1I1 hv1Zb1 hv1x hv1y hv2x hv3y hv3a3 hv3b3 hv2v3 hv2v1 hv3v1 hxorient
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit053

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
theorem N4dExcludesFormA_v1_of_layout
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S)
    (hB2 : S.N4dExcludesFormB_v2) :
    S.N4dExcludesFormA_v1 := by
  classical
  intro r hr hcard hesc hA
  rcases hA with ⟨x, y, hxI2, hyI3, hxeq, hyeq⟩
  have hxT1 : x ∈ S.witnessClassAt_v1 r := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).1
  rcases (p2mCoreSupport S).selectorShape_v2_split Z with ⟨s, hs, hT2card, hI2sub, hsplit2⟩
  have hxT2 : x ∈ S.witnessClassAt_v2 s := hI2sub hxI2
  have hcore := (p2mCoreSupport S).coreSelector_v1 hr hcard
  rcases hcore with ⟨-, hI1sub, -, -⟩
  have hnonendpoint :
      ∀ {p : ℝ²},
        p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) →
        p ≠ S.triangle.v3 →
        S.witnessClassAt_v2 s ∩ S.CP.C1 = ({p} : Finset ℝ²) →
        False := by
    intro p hp hp_ne_v3 hpC1
    have hpT2 : p ∈ S.witnessClassAt_v2 s := by
      have hpmem : p ∈ ({p} : Finset ℝ²) := by simp
      rw [← hpC1] at hpmem
      exact (Finset.mem_inter.mp hpmem).1
    have hpI1_or_v3 : p ∈ S.I1 ∨ p = S.triangle.v3 := by
      rcases Finset.mem_insert.mp hp with hpa1 | hp
      · left
        rw [hpa1, Z.hI1]
        simp
      rcases Finset.mem_insert.mp hp with hpb1 | hpv3
      · left
        rw [hpb1, Z.hI1]
        simp
      · right
        simpa using hpv3
    rcases hpI1_or_v3 with hpI1 | hpv3
    · have hpT1 : p ∈ S.witnessClassAt_v1 r := hI1sub hpI1
      have hpC1 : p ∈ S.CP.C1 := by
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hpI1).2).2
      have hxv1 : dist S.triangle.v1 x = r := by
        simpa using (Finset.mem_filter.mp hxT1).2
      have hpv1 : dist S.triangle.v1 p = r := by
        simpa using (Finset.mem_filter.mp hpT1).2
      have hxv2 : dist S.triangle.v2 x = s := by
        simpa using (Finset.mem_filter.mp hxT2).2
      have hpv2 : dist S.triangle.v2 p = s := by
        simpa using (Finset.mem_filter.mp hpT2).2
      have hxp : x ≠ p := by
        intro hxp
        have hxC2 : x ∈ S.CP.C2 := by
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).2
        have hxA : x ∈ A := S.CP.C2_subset hxC2
        have hx_ne_v1 : x ≠ S.triangle.v1 := (Finset.mem_erase.mp hxI2).1
        have hx_ne_v3 : x ≠ S.triangle.v3 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxI2).2).1
        have hx_ne_v2 : x ≠ S.triangle.v2 := by
          intro hxv2
          exact S.CP.v2_notin_C2 (by simpa [hxv2] using hxC2)
        have hxnonmoser : x ∉ S.triangle.verts := by
          simp [Problem97.MoserTriangle.verts, hx_ne_v1, hx_ne_v2, hx_ne_v3]
        have hxC1 : x ∈ S.CP.C1 := by
          simpa [hxp] using hpC1
        have hone := S.CP.nonmoser_in_one x hxA hxnonmoser
        by_cases hxC3 : x ∈ S.CP.C3
        · have : (3 : ℕ) = 1 := by
            simpa [hxC1, hxC2, hxC3] using hone
          omega
        · have : (2 : ℕ) = 1 := by
            simpa [hxC1, hxC2, hxC3] using hone
          omega
      have hx_side :
          0 < signedArea2 x S.triangle.v1 S.triangle.v2 *
            signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 :=
        (p2mCoreSupport S).c2_vertex_same_open_side_as_v3 hxI2
      have hp_side :
          0 < signedArea2 p S.triangle.v1 S.triangle.v2 *
            signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 :=
        c1_vertex_same_open_side_as_v3 S hpI1
      have hmid :
          signedArea2 (midpoint ℝ x p) S.triangle.v1 S.triangle.v2 = 0 :=
        twoCircle_midpoint_collinear
          (by simpa [dist_comm] using hpv1)
          (by simpa [dist_comm] using hxv1)
          (by simpa [dist_comm] using hpv2)
          (by simpa [dist_comm] using hxv2)
          hxp.symm
      have hreflect :
          signedArea2 p S.triangle.v1 S.triangle.v2 =
            -signedArea2 x S.triangle.v1 S.triangle.v2 :=
        signedArea2_reflection_neg
          (q := S.triangle.v1) (v2 := S.triangle.v2) (y := x) (u := p) hmid
      rw [hreflect] at hp_side
      linarith
    · exact False.elim (hp_ne_v3 hpv3)
  have hnonendpoint_or_endpoint :
      ∀ {p q : ℝ²},
        p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) →
        q ∈ S.I3 →
        S.witnessClassAt_v2 s ∩ S.CP.C1 = ({p} : Finset ℝ²) →
        S.witnessClassAt_v2 s ∩ S.CP.C3 = ({q} : Finset ℝ²) →
        False := by
    intro p q hp hqI3 hpC1 hqC3
    by_cases hpv3 : p = S.triangle.v3
    · have hs_pos : 0 < s := by
        have hv3T2 : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
          have hmem : p ∈ ({p} : Finset ℝ²) := by simp
          rw [← hpC1] at hmem
          rw [hpv3] at hmem
          exact (Finset.mem_inter.mp hmem).1
        have hv3dist : dist S.triangle.v2 S.triangle.v3 = s :=
          (Finset.mem_filter.mp hv3T2).2
        have hdist_pos : 0 < dist S.triangle.v2 S.triangle.v3 :=
          dist_pos.mpr S.triangle.v23_ne
        rwa [← hv3dist]
      have hcard2 : 4 ≤ (S.witnessClassAt_v2 s).card := by
        omega
      have hqT2 : q ∈ S.witnessClassAt_v2 s := by
        have hmem : q ∈ ({q} : Finset ℝ²) := by simp
        rw [← hqC3] at hmem
        exact (Finset.mem_inter.mp hmem).1
      have hqC3mem : q ∈ S.CP.C3 := by
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hqI3).2).2
      have hqA : q ∈ A := S.CP.C3_subset hqC3mem
      have hq_ne_v2 : q ≠ S.triangle.v2 := (Finset.mem_erase.mp hqI3).1
      have hq_ne_v1 : q ≠ S.triangle.v1 :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hqI3).2).1
      have hq_ne_v3 : q ≠ S.triangle.v3 := by
        intro h
        exact S.CP.v3_notin_C3 (by simpa [h] using hqC3mem)
      have hq_nonmoser : q ∉ S.triangle.verts := by
        simp [Problem97.MoserTriangle.verts, hq_ne_v1, hq_ne_v2, hq_ne_v3]
      have hq_not_C2 : q ∉ S.CP.C2 := by
        intro hqC2
        have hone := S.CP.nonmoser_in_one q hqA hq_nonmoser
        by_cases hqC1 : q ∈ S.CP.C1
        · have : (3 : ℕ) = 1 := by
            simpa [hqC1, hqC2, hqC3mem] using hone
          omega
        · have : (2 : ℕ) = 1 := by
            simpa [hqC1, hqC2, hqC3mem] using hone
          omega
      have hesc2 : ¬ S.witnessClassAt_v2 s ⊆ S.CP.C2 := by
        intro hsub
        exact hq_not_C2 (hsub hqT2)
      have hB : S.IsFormB_v2 s := by
        exact ⟨q, hqI3, hqC3, by simpa [hpv3] using hpC1⟩
      exact hB2 hs_pos hcard2 hesc2 hB
    · exact hnonendpoint hp hpv3 hpC1
  rcases hsplit2 with hqv1 | hqa3 | hqb3
  · rcases hqv1 with ⟨p, hp, hpC1, hpC3⟩
    by_cases hpv3 : p = S.triangle.v3
    · exact S.formA_v1_endpointPair_impossible Z hr hcard
        ⟨x, y, hxI2, hyI3, hxeq, hyeq⟩ hT2card hI2sub
        (by simpa [hpv3] using hpC1) hpC3
    · exact hnonendpoint hp hpv3 hpC1
  · rcases hqa3 with ⟨p, hp, hpC1, hpC3⟩
    have ha3I3 : Z.a3 ∈ S.I3 := by
      rw [Z.hI3]
      simp
    exact hnonendpoint_or_endpoint hp ha3I3 hpC1 hpC3
  · rcases hqb3 with ⟨p, hp, hpC1, hpC3⟩
    have hb3I3 : Z.b3 ∈ S.I3 := by
      rw [Z.hI3]
      simp
    exact hnonendpoint_or_endpoint hp hb3I3 hpC1 hpC3
theorem N4dExcludesFormA_v1_proof
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hB2 : S.N4dExcludesFormB_v2) :
    S.N4dExcludesFormA_v1 :=
  S.N4dExcludesFormA_v1_of_layout (p2mCoreSupport S).layout hB2
end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit054

open scoped EuclideanGeometry

/-- The escaped Form `a` at `v₁` is impossible for a finite endpoint shell. -/
theorem solution {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A)
    (_hB2 : S.N4dExcludesFormB_v2) :
    S.N4dExcludesFormA_v1 :=
  Batch3N9.Problem97.FiniteEndpointShell.N4dExcludesFormA_v1_proof S
    (Erdos9796FiniteNine.form_b_v2 S)
