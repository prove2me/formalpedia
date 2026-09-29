-- Prove2me | solution 1 for FamousTheorems.sign_hom_unique_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:46:37.536229+00:00
-- url     : https://prove2.me/submissions/f4bb5f37-bf40-496c-983f-e5427572ea4f

import Mathlib

theorem solution {α : Type*} [DecidableEq α] [Fintype α] (s : Equiv.Perm α →* ℤˣ) (hs : Function.Surjective s) :
    s = Equiv.Perm.sign :=
  Equiv.Perm.eq_sign_of_surjective_hom hs
