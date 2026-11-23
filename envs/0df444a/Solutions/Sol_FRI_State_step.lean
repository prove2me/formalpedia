-- Prove2me | solution 1 for FRI_State_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:21:58.213554+00:00
-- url     : https://prove2.me/submissions/57c33553-9986-42e1-800a-4f097e07ebf7

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i : ℕ) (h : i < P.num_foldings) :
    FRI_State P f_0 bound T (i + 1) ↔
    FRI_State P f_0 bound T i ∨
      FRI_BadEvent P f_0 bound ⟨i, h⟩ (FRI_oracle_at_round P f_0 T i h) (T.alpha ⟨i, h⟩) := by
  simp only [FRI_State, dif_pos h]
