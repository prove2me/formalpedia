-- Prove2me | solution 1 for BoydADMM.Nonconvex.boolean_projection
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T07:28:25.951739+00:00
-- url     : https://prove2.me/submissions/c5f974c1-af5e-4076-bbee-c8c4321e7349

import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_ProjectionBasics

open BoydADMM.Nonconvex

theorem solution {n : ℕ} (v : Fin n → ℝ) :
    roundBoolean v ∈ booleanSet ∧
    ∀ x ∈ booleanSet, sqDist (roundBoolean v) v ≤ sqDist x v := by
  refine ⟨?memb, ?opt⟩
  · intro i
    dsimp [roundBoolean]
    split_ifs <;> simp
  · intro x hx
    dsimp [sqDist]
    apply Finset.sum_le_sum
    intro i _
    have hb : x i = 0 ∨ x i = 1 := hx i
    dsimp [roundBoolean]
    split_ifs with hle
    · -- round → 0
      cases hb with
      | inl h0 =>
          simp [h0]
      | inr h1 =>
          -- (0 - v i)^2 ≤ (1 - v i)^2
          rw [h1]
          nlinarith
    · -- round → 1
      cases hb with
      | inl h0 =>
          -- (1 - v i)^2 ≤ (0 - v i)^2
          rw [h0]
          nlinarith
      | inr h1 =>
          simp [h1]
