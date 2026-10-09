-- Prove2me | solution 1 for BookProof.DampedOscillatorEnergy.coupledEnergy_not_constant_of_damped
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:46:43.56376+00:00
-- url     : https://prove2.me/submissions/698359dc-e4bc-49aa-ae4f-fea01e294188

-- Generated from ChapterDampedOscillatorEnergy.lean — solution of BookProof.DampedOscillatorEnergy.coupledEnergy_not_constant_of_damped
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
import Theorems.Thm_BookProof_DampedOscillatorEnergy_hasDerivAt_coupledEnergy
open BookProof.DampedOscillatorEnergy




open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution {lam1 lam2 omega1 omega2 c : ℝ}
    {x1 x2 v1 v2 a1 a2 : ℝ → ℝ} (hlam1 : 0 < lam1) (hlam2 : 0 ≤ lam2)
    (hx1 : ∀ t, HasDerivAt x1 (v1 t) t) (hx2 : ∀ t, HasDerivAt x2 (v2 t) t)
    (hv1 : ∀ t, HasDerivAt v1 (a1 t) t) (hv2 : ∀ t, HasDerivAt v2 (a2 t) t)
    (heq1 : ∀ t, a1 t + lam1 * v1 t + omega1 ^ 2 * x1 t - c * x2 t = 0)
    (heq2 : ∀ t, a2 t + lam2 * v2 t + omega2 ^ 2 * x2 t - c * x1 t = 0)
    {t₀ : ℝ} (hmove : v1 t₀ ≠ 0) :
    ¬ ∃ E : ℝ, ∀ t, coupledEnergy omega1 omega2 c x1 x2 v1 v2 t = E := by

  rintro ⟨E, hE⟩
  have hconst : HasDerivAt (coupledEnergy omega1 omega2 c x1 x2 v1 v2) 0 t₀ := by
    have hfun : coupledEnergy omega1 omega2 c x1 x2 v1 v2 = fun _ => E := funext hE
    rw [hfun]
    exact hasDerivAt_const t₀ E
  have hval := (hasDerivAt_coupledEnergy hx1 hx2 hv1 hv2 heq1 heq2 t₀).unique hconst
  have hsq : 0 < v1 t₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hmove))
  have hpos : 0 < lam1 * v1 t₀ ^ 2 := mul_pos hlam1 hsq
  have hnn : 0 ≤ lam2 * v2 t₀ ^ 2 := mul_nonneg hlam2 (sq_nonneg _)
  linarith
