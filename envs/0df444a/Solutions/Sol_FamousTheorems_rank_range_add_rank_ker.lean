-- Prove2me | solution 1 for FamousTheorems.rank_range_add_rank_ker
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:54.746777+00:00
-- url     : https://prove2.me/submissions/e8ae96ba-d984-41f0-aa3d-9fd698d23b03

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {R : Type u_2} {M M₁ : Type u_1} [inst : Ring R] [inst_1 : AddCommGroup M] 
    [inst_2 : AddCommGroup M₁] [inst_3 : Module R M] [inst_4 : Module R M₁] [HasRankNullity.{u_1, u_2} R] 
    (f : M →ₗ[R] M₁), Module.rank R ↥f.range + Module.rank R ↥f.ker = Module.rank R M :=
  @_root_.LinearMap.rank_range_add_rank_ker
