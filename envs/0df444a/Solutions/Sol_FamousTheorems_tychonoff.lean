-- Prove2me | solution 1 for FamousTheorems.tychonoff
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T06:56:13.585706+00:00
-- url     : https://prove2.me/submissions/ea42429a-9934-4c22-b9f2-619bf5ec6623

import Mathlib

open Filter Set Topology

theorem solution {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {s : ∀ i, Set (X i)} (h : ∀ i, IsCompact (s i)) :
    IsCompact { x : ∀ i, X i | ∀ i, x i ∈ s i } := isCompact_pi_infinite h
