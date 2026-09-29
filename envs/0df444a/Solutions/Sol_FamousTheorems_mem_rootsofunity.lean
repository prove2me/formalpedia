-- Prove2me | solution 1 for FamousTheorems.mem_rootsofunity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:46.997605+00:00
-- url     : https://prove2.me/submissions/006ce85c-d0ba-4f9b-af0c-a0e991f04183

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ (n : ℕ) [NeZero n] (x : ℂˣ), 
    x ∈ rootsOfUnity n ℂ ↔ ∃ i < n, Complex.exp (2 * ↑Real.pi * Complex.I * (↑i / ↑n)) = ↑x :=
  @_root_.Complex.mem_rootsOfUnity
