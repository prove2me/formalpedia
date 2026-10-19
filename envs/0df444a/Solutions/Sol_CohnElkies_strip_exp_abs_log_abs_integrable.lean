-- Prove2me | solution 1 for CohnElkies.strip_exp_abs_log_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/c71f7eb6-5210-47df-b262-799d46a04b20

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_strip_exp_abs_log_integrableOn_Ioi
import Theorems.Thm_CohnElkies_strip_exp_abs_log_integrableOn_Iio

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    Integrable
      (fun x : ℝ =>
        Real.exp ((-a) * |x|) * |Real.log (|x|)|) := by
  have hright :
      IntegrableOn
        (fun x : ℝ =>
          Real.exp ((-a) * |x|) * |Real.log (|x|)|)
        (Ioi (0 : ℝ)) := by
    refine (strip_exp_abs_log_integrableOn_Ioi ha).congr_fun ?_
      measurableSet_Ioi
    intro x hx
    try dsimp
    rw [abs_of_pos (mem_Ioi.mp hx)]
  have hleft :
      IntegrableOn
        (fun x : ℝ =>
          Real.exp ((-a) * |x|) * |Real.log (|x|)|)
        (Iio (0 : ℝ)) := by
    refine (strip_exp_abs_log_integrableOn_Iio ha).congr_fun ?_
      measurableSet_Iio
    intro x hx
    try dsimp
    rw [abs_of_neg (mem_Iio.mp hx)]
    simp [mul_neg, neg_mul]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩
end CohnElkies
