-- Prove2me | solution 1 for FamousTheorems.frattini_subgroup_nilpotent_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:04:44.96198+00:00
-- url     : https://prove2.me/submissions/6ff8a7e7-e65b-4817-a71a-03f84be5ab5a

import Mathlib

theorem solution {G : Type*} [Group G] [Finite G] : Group.IsNilpotent (frattini G) :=
  frattini_nilpotent
