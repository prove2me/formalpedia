-- Prove2me | solution 1 for FamousTheorems.cayley
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T01:51:16.475646+00:00
-- url     : https://prove2.me/submissions/38a7517c-59ac-4a2b-9de7-50b2f813704c

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem solution (G H : Type*) [Group G] [MulAction G H] [FaithfulSMul G H] :
    Nonempty (G ≃* (MulAction.toPermHom G H).range) :=
  ⟨Equiv.Perm.subgroupOfMulAction G H⟩
