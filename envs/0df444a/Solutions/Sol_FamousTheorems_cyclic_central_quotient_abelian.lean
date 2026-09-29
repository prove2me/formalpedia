-- Prove2me | solution 1 for FamousTheorems.cyclic_central_quotient_abelian
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:02:02.056791+00:00
-- url     : https://prove2.me/submissions/4705c6bf-1917-469e-8d3e-d7775f49830c

import Mathlib

theorem solution (G : Type*) [Group G] [IsCyclic (G ⧸ Subgroup.center G)] : IsMulCommutative G :=
  isMulCommutative_of_isCyclic_quotient_center_self G
