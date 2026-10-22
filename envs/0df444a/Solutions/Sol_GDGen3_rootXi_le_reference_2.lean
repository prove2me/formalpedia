-- Prove2me | solution 2 for GDGen3.rootXi_le_reference
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:43:03.379988+00:00
-- url     : https://prove2.me/submissions/2abb80af-7e1f-461b-bf29-f0eb84ed5796

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_X_pos
import Theorems.Thm_GDGen3_rootXi_zero
import Theorems.Thm_GDGen3_rootXi_pos
import Theorems.Thm_GDGen3_rootXi_quad
import Theorems.Thm_GDGen3_M_le_h
import Theorems.Thm_GDGen3_referenceXi_zero
import Theorems.Thm_GDGen3_referenceXi_pos
import Theorems.Thm_GDGen3_referenceXi_lt_half
import Theorems.Thm_GDGen3_referenceXi_quad
import Theorems.Thm_GDGen3_rootPoly_parameter
import Theorems.Thm_GDGen3_rootPoly_actual
import Theorems.Thm_GDGen3_quadratic_root_le

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hiN : i < N) (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    rootXi r N i ≤ referenceXi r i := by
  by_cases hi : i = 0
  · subst i; rw [rootXi_zero, referenceXi_zero r hr]
  · have hi1 : 1 ≤ i := by omega
    have hp := pj_pos r hr hr1 (i + 1) (by omega)
    have hx := X_pos r hr hr1 N i hi1 hiN
    have hxi := rootXi_pos r hr hr1 N i hi
    have href := referenceXi_pos r hr hr1 N i hi1 hiN hbranch
    have hm := M_le_h r hr hr1 N (by omega) hbranch
    have hhalf := referenceXi_lt_half r hr hr1 i hi1
    have hpoly : 0 ≤ rootPoly r (M r N) i (referenceXi r i) := by
      rw [rootPoly_parameter r hr hr1, referenceXi_quad r hr hr1, zero_add]
      apply mul_nonneg
      · apply div_nonneg (by positivity) (by positivity)
      · linarith
    rw [rootPoly_actual] at hpoly
    have hroot := rootXi_quad r hr hr1 N i hiN
    unfold eta at hroot
    apply quadratic_root_le (pj r (i + 1)) (pj r (i + 1) * (1 + C r N i)) (X r N i)
      (rootXi r N i) (referenceXi r i) hp hx hxi (le_of_lt href)
    · nlinarith [hroot]
    · nlinarith [hpoly]
