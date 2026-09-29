-- Prove2me | solution 1 for FamousTheorems.yoneda_embedding_full_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:24:17.22285+00:00
-- url     : https://prove2.me/submissions/5682fb38-99a5-481a-9d45-ecc8a46a97c3

import Mathlib

open CategoryTheory

theorem solution (C : Type*) [Category C] : (yoneda : C ⥤ Cᵒᵖ ⥤ Type _).Full :=
  inferInstance
