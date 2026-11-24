-- Prove2me | solution 1 for Formalism.GM.bB_succ_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:34.992919+00:00
-- url     : https://prove2.me/submissions/46ea3856-26f2-46ce-a0a8-0e282f20f6f5

import Definitions.Def_Formalism_MahlerMeasure_StatementB
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Polynomial
namespace Formalism.GM
theorem _root_.solution (c : ℚ) (i : ℕ) : bB c (i + 1) 0 = C (c / (i + 1 : ℕ)) * X * bB c i (-1) := by
  simp only [bB]
  rw [descPochhammer_succ_left, mul_comp, X_comp, comp_assoc, sub_comp, X_comp, one_comp,
    Nat.factorial_succ]
  have hf : ((i.factorial : ℚ)) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
  have e1 : C c * X + C (((0 : ℤ)) : ℚ) - 1 = C c * X + C (((-1 : ℤ)) : ℚ) := by
    simp only [Int.cast_zero, C_0, add_zero, Int.cast_neg, Int.cast_one, C_neg, C_1]
    ring
  rw [e1]
  have hC : C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * C c = C (c / ((i + 1 : ℕ) : ℚ)) * C ((i.factorial : ℚ)⁻¹) := by
    rw [← C_mul, ← C_mul]
    congr 1
    push_cast
    field_simp
  simp only [Int.cast_zero, C_0, add_zero]
  calc C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * (C c * X * (descPochhammer ℚ i).comp (C c * X + C (((-1 : ℤ)) : ℚ)))
      = (C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * C c) * X * (descPochhammer ℚ i).comp (C c * X + C (((-1 : ℤ)) : ℚ)) := by ring
    _ = _ := by rw [hC]; ring
end Formalism.GM
