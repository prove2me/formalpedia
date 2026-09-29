-- Prove2me | solution 1 for FamousTheorems.level_one_modular_forms_dimension_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:10:52.896027+00:00
-- url     : https://prove2.me/submissions/15f21cc3-42e0-4fc6-9981-3338a60c3c83

import Mathlib

theorem solution (k : ℕ) (hk : Even k) :
    Module.rank ℂ (ModularForm (MonoidHom.range (Matrix.SpecialLinearGroup.mapGL ℝ :
        Matrix.SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℝ)) (k : ℤ)) =
      ((if k ≡ 2 [MOD 12] then k / 12 else k / 12 + 1 : ℕ) : Cardinal) :=
  ModularForm.dimension_level_one k hk
