-- Prove2me | solution 1 for FamousTheorems.krull_maximal_ideal_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:42:03.157645+00:00
-- url     : https://prove2.me/submissions/2a9f42d3-c054-4528-a010-4b963d9a984a

import Mathlib

theorem solution {R : Type*} [Semiring R] (I : Ideal R) (hI : I ≠ ⊤) : ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M :=
  Ideal.exists_le_maximal I hI
