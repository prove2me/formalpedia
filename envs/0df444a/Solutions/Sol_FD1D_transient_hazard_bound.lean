-- Prove2me | solution 1 for FD1D.transient_hazard_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:27.472179+00:00
-- url     : https://prove2.me/submissions/cde2e42d-0179-4cb7-8206-bccb0ec03131

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    {a L m T H logTerm : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hT : 0 < T)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hlog : 0 ≤ logTerm)
    (haL : 200 * L ≤ a) (hlogA : 200 * logTerm ≤ a)
    (hmain :
      (a / 100 - L) * H ≤
        103 * a / (300 * m ^ 2) + logTerm / T) :
    H ≤ 206 / (3 * m ^ 2) + 1 / T := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hcoef : a / 200 ≤ a / 100 - L := by linarith
  have ha200 : 0 < a / 200 := by positivity
  have hscaled :
      (a / 200) * H ≤
        103 * a / (300 * m ^ 2) + logTerm / T := by
    calc
      (a / 200) * H ≤ (a / 100 - L) * H :=
        mul_le_mul_of_nonneg_right hcoef hH
      _ ≤ _ := hmain
  have hlogScaled : logTerm / T ≤ (a / 200) * (1 / T) := by
    apply (div_le_iff₀ hT).2
    field_simp
    nlinarith
  apply (mul_le_mul_iff_of_pos_left ha200).mp
  calc
    a / 200 * H ≤
        103 * a / (300 * m ^ 2) + logTerm / T := hscaled
    _ ≤ a / 200 * (206 / (3 * m ^ 2)) +
        a / 200 * (1 / T) := by
      apply add_le_add
      · field_simp
        norm_num
      · exact hlogScaled
    _ = a / 200 * (206 / (3 * m ^ 2) + 1 / T) := by ring
end FD1D
