-- Prove2me | solution 1 for FamousTheorems.modular_fundamental_domain_covers_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:13:47.236409+00:00
-- url     : https://prove2.me/submissions/59feca9e-79c1-4c67-a1c4-cd473b67489d

import Mathlib

theorem solution (z : UpperHalfPlane) : ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℤ, g • z ∈ ModularGroup.fd :=
  ModularGroup.exists_smul_mem_fd z
