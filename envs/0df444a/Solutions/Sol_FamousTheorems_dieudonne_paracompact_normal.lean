-- Prove2me | solution 1 for FamousTheorems.dieudonne_paracompact_normal
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:24:51.570185+00:00
-- url     : https://prove2.me/submissions/bf5e01a7-7671-4729-8902-a785676e1c67

import Mathlib

theorem solution {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] :
    NormalSpace X :=
  NormalSpace.of_paracompactSpace_r1Space
