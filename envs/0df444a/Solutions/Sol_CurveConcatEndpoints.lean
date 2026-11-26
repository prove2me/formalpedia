-- Prove2me | solution 1 for CurveConcatEndpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:15.594897+00:00
-- url     : https://prove2.me/submissions/4f45de94-6437-4d12-8617-6dcdaf0b65b7

import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_CurveConcatEndpoints

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ₁ γ₂ : Curve E)
    (h : γ₁.toFun γ₁.len = γ₂.toFun 0) :
    (curveConcat γ₁ γ₂ h).toFun 0 = γ₁.toFun 0 ∧
      (curveConcat γ₁ γ₂ h).toFun (curveConcat γ₁ γ₂ h).len = γ₂.toFun γ₂.len := by
-- BODY
  constructor
  · show (if (0:ℝ) ≤ γ₁.len then γ₁.toFun 0 else γ₂.toFun (0 - γ₁.len)) = γ₁.toFun 0
    rw [if_pos γ₁.len_nonneg]
  · show (if γ₁.len + γ₂.len ≤ γ₁.len then γ₁.toFun (γ₁.len + γ₂.len)
          else γ₂.toFun (γ₁.len + γ₂.len - γ₁.len)) = γ₂.toFun γ₂.len
    rcases eq_or_lt_of_le γ₂.len_nonneg with hb0 | hbpos
    · rw [if_pos (by linarith)]
      simpa [← hb0] using h
    · rw [if_neg (by linarith)]
      congr 1
      ring
