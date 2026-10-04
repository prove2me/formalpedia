-- Prove2me | solution 1 for Conway99Formal.LiteratureCensusErrors.solution
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T00:27:46.360562+00:00
-- url     : https://prove2.me/submissions/fac02596-9f05-4478-ab9c-c509581669a0

import Definitions.Def_Conway99_Literature_Census_20261003

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace Conway99Formal.LiteratureCensusErrors

theorem block01_at_99_14 (x y : ℚ) :
    block01 99 14 x y = 448371 + (-20) * x + (2) * y := by
  norm_num [block01, z001, z002, z003, z004, z005, z006, z007, z008, z009, z010, z011, z012, z013, z014, z015, z016] <;> ring

theorem block02_at_99_14 (x y : ℚ) :
    block02 99 14 x y = 3118500 + (138) * x + (-7) * y := by
  norm_num [block02, z017, z018, z019, z020, z021, z022, z023, z024, z025, z026, z027, z028, z029, z030, z031, z032] <;> ring

theorem block03_at_99_14 (x y : ℚ) :
    block03 99 14 x y = 3797640 + (-18) * x + ((-17 / 4 : ℚ)) * y := by
  norm_num [block03, z033, z034, z035, z036, z037, z038, z039, z040, z041, z042, z043, z044, z045, z046, z047, z048] <;> ring

theorem block04_at_99_14 (x y : ℚ) :
    block04 99 14 x y = 13471920 + (-290) * x + ((25 / 2 : ℚ)) * y := by
  norm_num [block04, z049, z050, z051, z052, z053, z054, z055, z056, z057, z058, z059, z060, z061, z062, z063, z064] <;> ring

theorem block05_at_99_14 (x y : ℚ) :
    block05 99 14 x y = 16798320 + (-211) * x + ((73 / 4 : ℚ)) * y := by
  norm_num [block05, z065, z066, z067, z068, z069, z070, z071, z072, z073, z074, z075, z076, z077, z078, z079, z080] <;> ring

theorem block06_at_99_14 (x y : ℚ) :
    block06 99 14 x y = 30945915 + (7) * x + ((-25 / 4 : ℚ)) * y := by
  norm_num [block06, z081, z082, z083, z084, z085, z086, z087, z088, z089, z090, z091, z092, z093, z094, z095, z096] <;> ring

theorem block07_at_99_14 (x y : ℚ) :
    block07 99 14 x y = 69729660 + (227) * x + ((-141 / 4 : ℚ)) * y := by
  norm_num [block07, z097, z098, z099, z100, z101, z102, z103, z104, z105, z106, z107, z108, z109, z110, z111, z112] <;> ring

theorem block08_at_99_14 (x y : ℚ) :
    block08 99 14 x y = 67442760 + (401) * x + ((-49 / 2 : ℚ)) * y := by
  norm_num [block08, z113, z114, z115, z116, z117, z118, z119, z120, z121, z122, z123, z124, z125, z126, z127, z128] <;> ring

theorem block09_at_99_14 (x y : ℚ) :
    block09 99 14 x y = 311145912 + (-812) * x + (48) * y := by
  norm_num [block09, z129, z130, z131, z132, z133, z134, z135, z136, z137, z138, z139, z140, z141, z142, z143, z144] <;> ring

theorem block10_at_99_14 (x y : ℚ) :
    block10 99 14 x y = 218468250 + (124) * x + ((133 / 4 : ℚ)) * y := by
  norm_num [block10, z145, z146, z147, z148, z149, z150, z151, z152, z153, z154, z155, z156, z157, z158, z159, z160] <;> ring

theorem block11_at_99_14 (x y : ℚ) :
    block11 99 14 x y = 740773044 + (573) * x + (-16) * y := by
  norm_num [block11, z161, z162, z163, z164, z165, z166, z167, z168, z169, z170, z171, z172, z173, z174, z175, z176] <;> ring

theorem block12_at_99_14 (x y : ℚ) :
    block12 99 14 x y = 1739079342 + (-216) * x + (-56) * y := by
  norm_num [block12, z177, z178, z179, z180, z181, z182, z183, z184, z185, z186, z187, z188, z189, z190, z191, z192] <;> ring

theorem block13_at_99_14 (x y : ℚ) :
    block13 99 14 x y = 11577777750 + (97) * x + ((141 / 4 : ℚ)) * y := by
  norm_num [block13, z193, z194, z195, z196, z197, z198, z199, z200, z201, z202, z203, z204, z205, z206, z207, z208] <;> ring

theorem printed_total_at_99_14 (x y : ℚ) :
    printedTotal 99 14 x y = 14792997384 := by
  simp only [printedTotal, block01_at_99_14, block02_at_99_14, block03_at_99_14, block04_at_99_14, block05_at_99_14, block06_at_99_14, block07_at_99_14, block08_at_99_14, block09_at_99_14, block10_at_99_14, block11_at_99_14, block12_at_99_14, block13_at_99_14]
  ring

theorem seven_set_total : Nat.choose 99 7 = 14887031544 := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega : 7 ≤ 99)]
  norm_num [Nat.factorial]

theorem printed_shortfall (x y : ℚ) :
    (Nat.choose 99 7 : ℚ) - printedTotal 99 14 x y = 94034160 := by
  rw [seven_set_total, printed_total_at_99_14]
  norm_num

theorem printed_total_ne_seven_sets (x y : ℚ) :
    printedTotal 99 14 x y ≠ (Nat.choose 99 7 : ℚ) := by
  rw [seven_set_total, printed_total_at_99_14]
  norm_num

theorem z176_at_243_22 (x y : ℚ) :
    z176 243 22 x y = 11258676000 / 7 + 456 * x - 9 * y := by
  norm_num [z176] <;> ring

theorem z176_numerator_mod_seven : (11258676000 : ℤ) % 7 = 5 := by
  norm_num

theorem z176_nonintegral (x y : ℤ) :
    ¬ ∃ z : ℤ, (z : ℚ) = z176 243 22 x y := by
  rintro ⟨z, hz⟩
  rw [z176_at_243_22] at hz
  have hq : (7 : ℚ) * z = 11258676000 + 7 * (456 * (x : ℚ) - 9 * (y : ℚ)) := by
    linear_combination 7 * hz
  have hi : 7 * z = 11258676000 + 7 * (456 * x - 9 * y) := by
    exact_mod_cast hq
  omega

theorem solution (x y : ℤ) :
    printedTotal 99 14 (x : ℚ) (y : ℚ) = 14792997384 ∧
    (Nat.choose 99 7 : ℚ) - printedTotal 99 14 (x : ℚ) (y : ℚ) = 94034160 ∧
    ¬ ∃ z : ℤ, (z : ℚ) = z176 243 22 x y := by
  exact ⟨printed_total_at_99_14 _ _, printed_shortfall _ _, z176_nonintegral x y⟩

end Conway99Formal.LiteratureCensusErrors

open Conway99Formal.LiteratureCensusErrors

theorem solution (x y : ℤ) :
    printedTotal 99 14 (x : ℚ) (y : ℚ) = 14792997384 ∧
    (Nat.choose 99 7 : ℚ) - printedTotal 99 14 (x : ℚ) (y : ℚ) = 94034160 ∧
    ¬ ∃ z : ℤ, (z : ℚ) = z176 243 22 x y := by
  exact Conway99Formal.LiteratureCensusErrors.solution x y

#print axioms solution
