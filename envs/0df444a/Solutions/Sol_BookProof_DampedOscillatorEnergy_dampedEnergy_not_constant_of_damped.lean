-- Prove2me | solution 1 for BookProof.DampedOscillatorEnergy.dampedEnergy_not_constant_of_damped
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:46:04.069171+00:00
-- url     : https://prove2.me/submissions/dbe361fb-a602-43be-b95d-5a94a7661c7f

-- Generated from ChapterDampedOscillatorEnergy.lean — solution of BookProof.DampedOscillatorEnergy.dampedEnergy_not_constant_of_damped
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
import Theorems.Thm_BookProof_DampedOscillatorEnergy_hasDerivAt_dampedEnergy
open BookProof.DampedOscillatorEnergy




open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution {lam omega : ℝ} {x v a : ℝ → ℝ}
    (hlam : 0 < lam) (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, a t + lam * v t + omega ^ 2 * x t = 0) {t₀ : ℝ} (hmove : v t₀ ≠ 0) :
    ¬ ∃ E : ℝ, ∀ t, dampedEnergy omega x v t = E := by

  rintro ⟨E, hE⟩
  have hconst : HasDerivAt (dampedEnergy omega x v) 0 t₀ := by
    have : dampedEnergy omega x v = fun _ => E := funext hE
    rw [this]
    exact hasDerivAt_const t₀ E
  have hval := (hasDerivAt_dampedEnergy hx hv heq t₀).unique hconst
  have hsq : 0 < v t₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hmove))
  have hpos : 0 < lam * v t₀ ^ 2 := mul_pos hlam hsq
  linarith
