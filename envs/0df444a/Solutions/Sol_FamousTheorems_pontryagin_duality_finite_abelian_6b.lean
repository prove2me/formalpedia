-- Prove2me | solution 1 for FamousTheorems.pontryagin_duality_finite_abelian_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:46:05.233835+00:00
-- url     : https://prove2.me/submissions/d821ff73-ba71-4a0e-872d-841d1b64d8e2

import Mathlib

theorem solution {α : Type*} [AddCommGroup α] [Finite α] :
    Function.Bijective (AddChar.doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) :=
  AddChar.doubleDualEmb_bijective
