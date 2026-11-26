-- Prove2me | solution 1 for FD1D.stationary_hazard_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:13.671199+00:00
-- url     : https://prove2.me/submissions/c585ed40-8bea-4b04-b3f2-3f44a8e32efe

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    {a L m H : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (haL : 200 * L ≤ a)
    (hmain :
      (a / 100 - L) * H ≤ 103 * a / (300 * m ^ 2)) :
    H ≤ 206 / (3 * m ^ 2) := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hcoef : a / 200 ≤ a / 100 - L := by
    linarith
  have ha200 : 0 < a / 200 := by positivity
  have hscaled : (a / 200) * H ≤ 103 * a / (300 * m ^ 2) := by
    calc
      (a / 200) * H ≤ (a / 100 - L) * H :=
        mul_le_mul_of_nonneg_right hcoef hH
      _ ≤ _ := hmain
  apply (mul_le_mul_iff_of_pos_left ha200).mp
  calc
    a / 200 * H ≤ 103 * a / (300 * m ^ 2) := hscaled
    _ = a / 200 * (206 / (3 * m ^ 2)) := by
      field_simp
      <;> ring
end FD1D
