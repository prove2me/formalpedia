-- Prove2me | solution 1 for BookProof.ChapterGaugeAdjointAlgebra.inner_adjVar_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:24:05.836792+00:00
-- url     : https://prove2.me/submissions/09a39c72-0276-4428-8642-3ecc28915038

-- Generated from ChapterGaugeAdjointAlgebra.lean — solution of BookProof.ChapterGaugeAdjointAlgebra.inner_adjVar_self_eq_zero
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra





open Finset

variable {L : Type*} [LieRing L]

variable {L : Type*} [LieRing L]

set_option maxHeartbeats 1000000 in
theorem solution {κ : L → L → ℝ}
    (hinv : ∀ x y z : L, κ ⁅x, z⁆ y + κ x ⁅y, z⁆ = 0)
    (hsymm : ∀ x y : L, κ x y = κ y x) (x θ : L) : κ ⁅x, θ⁆ x = 0 := by

  have h := hinv x x θ
  rw [hsymm x ⁅x, θ⁆] at h
  linarith
