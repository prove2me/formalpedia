-- Prove2me | solution 1 for BBCode.new_codes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:34:29.705076+00:00
-- url     : https://prove2.me/submissions/a86cac5c-87af-4aa7-8375-160bfcae3ef1

import Theorems.Thm_BBCode_new336_class1_params
import Theorems.Thm_BBCode_new336_class2_params
import Theorems.Thm_BBCode_new360_params
open BBCode

theorem solution :
    IsCode (l := 2) (m := 84) {(0, 0), (0, 1), (1, 5)} {(0, 0), (0, 4), (0, 62)} 336 20 12 ∧
    IsCode (l := 2) (m := 84) {(0, 0), (0, 1), (1, 5)} {(0, 0), (0, 20), (0, 46)} 336 20 12 ∧
    IsCode (l := 6) (m := 30) {(0, 0), (0, 1), (1, 2)} {(0, 0), (0, 8), (2, 16)} 360 24 12 := by
  exact ⟨BBCode.new336_class1_params, BBCode.new336_class2_params, BBCode.new360_params⟩

#print axioms solution
