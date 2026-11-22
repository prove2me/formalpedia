-- Prove2me | solution 1 for GJKKL.Numerics.tangent_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:31.601493+00:00
-- url     : https://prove2.me/submissions/11b4ef99-c08d-441e-bc00-8ea3cb36b886

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real
namespace GJKKL.Numerics
theorem _root_.solution {a u : ℝ} (ha : 0 < a) (hu : 1 ≤ u) :
    u * log (u / a) - (u - 1) * log ((u - 1) / a) - 1 ≤ log (u / a) := by
  rcases hu.lt_or_eq with hu1 | hu1
  · have hu0 : 0 < u := by linarith
    have hv0 : 0 < u - 1 := by linarith
    rw [log_div hu0.ne' ha.ne', log_div hv0.ne' ha.ne']
    have hlog : log u - log (u - 1) ≤ 1 / (u - 1) := by
      rw [← log_div hu0.ne' hv0.ne']
      have := log_le_sub_one_of_pos (show 0 < u / (u - 1) by positivity)
      have h2 : u / (u - 1) - 1 = 1 / (u - 1) := by field_simp; ring
      linarith
    have h3 : (u - 1) * (log u - log (u - 1)) ≤ 1 := by
      calc (u - 1) * (log u - log (u - 1)) ≤ (u - 1) * (1 / (u - 1)) :=
            mul_le_mul_of_nonneg_left hlog hv0.le
        _ = 1 := by field_simp
    nlinarith
  · subst hu1
    simp
end GJKKL.Numerics
