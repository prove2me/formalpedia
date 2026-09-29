-- Prove2me | solution 1 for FamousTheorems.nerve_is_quasicategory_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:03:26.159988+00:00
-- url     : https://prove2.me/submissions/77d462ee-34c4-4c16-8d0c-bede8da4e5d2

import Mathlib

theorem solution (C : Type*) [CategoryTheory.Category C] : (CategoryTheory.nerve C).Quasicategory :=
  CategoryTheory.Nerve.quasicategory
