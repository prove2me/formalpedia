-- Prove2me | solution 1 for FamousTheorems.yang_baxter_braided_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:05:37.073984+00:00
-- url     : https://prove2.me/submissions/53dd2815-2763-4c19-a09c-aae39583d173

import Mathlib

open CategoryTheory MonoidalCategory

theorem solution {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv ≫
        (β_ Y Z).hom ▷ X ≫ (α_ Z Y X).hom =
      X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom ≫ Z ◁ (β_ X Y).hom :=
  BraidedCategory.yang_baxter X Y Z
