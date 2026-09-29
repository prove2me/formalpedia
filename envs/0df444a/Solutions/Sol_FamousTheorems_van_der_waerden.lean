-- Prove2me | solution 1 for FamousTheorems.van_der_waerden
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:31:25.897281+00:00
-- url     : https://prove2.me/submissions/2db196db-e10f-476c-a258-576ca2889311

import Mathlib

theorem solution {M κ : Type*} [AddCommMonoid M] (S : Finset M) [Finite κ] (C : M → κ) :
    ∃ a > 0, ∃ (b : M) (c : κ), ∀ s ∈ S, C (a • s + b) = c :=
  Combinatorics.exists_mono_homothetic_copy S C
