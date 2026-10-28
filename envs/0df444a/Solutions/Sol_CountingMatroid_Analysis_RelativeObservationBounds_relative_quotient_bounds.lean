-- Prove2me | solution 1 for CountingMatroid.Analysis.RelativeObservationBounds.relative_quotient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:05:02.252237+00:00
-- url     : https://prove2.me/submissions/2090341a-98e2-4dfb-98f8-c3d419375262

import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace CountingMatroid.Analysis.RelativeObservationBounds
end CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: Two positive means estimated with relative error at most η
have an empirical quotient within the paper's ratio interval. This is
arithmetic and assumes no independence of the observations.
TEXLINE: main.tex:1257-1270,1290-1304 -/
theorem solution (η a b x y : ℚ)
    (hη : 0 ≤ η) (hηlt : η < 1) (ha : 0 < a) (hb : 0 < b)
    (hx : RelativeEstimate η a x) (hy : RelativeEstimate η b y) :
    0 < x ∧ 0 < y ∧
      (1 - η) / (1 + η) ≤ (x / y) / (a / b) ∧
      (x / y) / (a / b) ≤ (1 + η) / (1 - η) := by
  have hm : 0 < 1 - η := sub_pos.mpr hηlt
  have hp : 0 < 1 + η := by linarith
  have hxp : 0 < x := (mul_pos hm ha).trans_le hx.1
  have hyp : 0 < y := (mul_pos hm hb).trans_le hy.1
  refine ⟨hxp, hyp, ?_, ?_⟩
  · apply (le_div_iff₀ (div_pos ha hb)).mpr
    have he : (1 - η) / (1 + η) * (a / b) =
        ((1 - η) * a) / ((1 + η) * b) := by
          rw [div_mul_div_comm]
    rw [he]
    exact div_le_div₀ hxp.le hx.1 hyp hy.2
  · apply (div_le_iff₀ (div_pos ha hb)).mpr
    have he : (1 + η) / (1 - η) * (a / b) =
        ((1 + η) * a) / ((1 - η) * b) := by
          rw [div_mul_div_comm]
    rw [he]
    exact div_le_div₀ (by positivity) hx.2 (mul_pos hm hb) hy.1
