-- Prove2me | solution 1 for FamousTheorems.higher_homotopy_groups_abelian_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:02:55.657372+00:00
-- url     : https://prove2.me/submissions/9d6c943d-ab5d-4a9d-9322-112c672f5c7e

import Mathlib

theorem solution (N : Type*) {X : Type*} [TopologicalSpace X] (x : X) [DecidableEq N] [Nontrivial N]
    (a b : HomotopyGroup N X x) : a * b = b * a :=
  mul_comm a b
