-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.diffusionCoeffs_lipschitz_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:22.110002+00:00
-- url     : https://prove2.me/submissions/eadabf3d-1ea6-4d71-89dd-79246db8a4f3

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
universe u
 theorem solution {N d : ℕ}
    {b : (Fin N → ℝ) → Fin N → ℝ}
    {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {K : ℝ≥0}
    (hb : LipschitzWith K b) (hσ : ∀ k, LipschitzWith K fun x => σ x k) :
    ∃ L : ℝ, (FunctionalInequalities.Probability.Diffusion.diffusionCoeffs b σ).IsLipschitz (0 : Measure Unit) L := by
  classical
  let c : ℝ := (N : ℝ) * (d : ℝ)
  let L : ℝ := (c + 1) * (K : ℝ)
  have hc : 0 ≤ c := by positivity
  have hk : 0 ≤ (K : ℝ) := by positivity
  have hKL : (K : ℝ) ≤ L := by
    dsimp [L]
    nlinarith [mul_nonneg hc hk]
  have hL : 0 ≤ L := hk.trans hKL
  have hfac : c ≤ (c + 1) ^ 2 := by nlinarith
  have hsq : c * (K : ℝ) ^ 2 ≤ L ^ 2 := by
    calc
      c * (K : ℝ) ^ 2 ≤ (c + 1) ^ 2 * (K : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hfac (sq_nonneg _)
      _ = L ^ 2 := (mul_pow _ _ _).symm
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro _ x y
    exact (hb.norm_sub_le x y).trans
      (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))
  · intro _ x y
    have hp : ∀ i k, (σ x k i - σ y k i) ^ 2 ≤
        (K : ℝ) ^ 2 * ‖x - y‖ ^ 2 := by
      intro i k
      have hh : |σ x k i - σ y k i| ≤ (K : ℝ) * ‖x - y‖ :=
        (norm_le_pi_norm (σ x k - σ y k) i).trans ((hσ k).norm_sub_le x y)
      have hh' := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
      simpa only [sq_abs, mul_pow] using hh'
    change (∑ i, ∑ k, (σ x k i - σ y k i) ^ 2) ≤ L ^ 2 * ‖x - y‖ ^ 2
    calc
      (∑ i, ∑ k, (σ x k i - σ y k i) ^ 2) ≤
          ∑ _i : Fin N, ∑ _k : Fin d, (K : ℝ) ^ 2 * ‖x - y‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hp i k
      _ = c * (K : ℝ) ^ 2 * ‖x - y‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [c]
        ring
      _ ≤ L ^ 2 * ‖x - y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  · intro _ _ _
    change (∫⁻ _e, _ ∂(0 : Measure Unit)) ≤ _
    simp
