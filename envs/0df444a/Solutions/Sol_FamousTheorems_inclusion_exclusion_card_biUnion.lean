-- Prove2me | solution 1 for FamousTheorems.inclusion_exclusion_card_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:42:29.949079+00:00
-- url     : https://prove2.me/submissions/b811ce53-590e-4b28-b45a-9443782637e8

import Mathlib

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Real Topology EuclideanGeometry RealInnerProductSpace Affine

theorem solution {ι α : Type*} [DecidableEq α] (s : Finset ι) (S : ι → Finset α) :
    (s.biUnion S).card = ∑ t : {t ∈ s.powerset | t.Nonempty},
      (-1 : ℤ) ^ (t.1.card + 1) * (t.1.inf' (Finset.mem_filter.1 t.2).2 S).card :=
  Finset.inclusion_exclusion_card_biUnion s S

section EuclideanGeom
variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]
