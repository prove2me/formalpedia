-- Prove2me | solution 1 for BosonicLearn.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:14:22.097192+00:00
-- url     : https://prove2.me/submissions/7a6da3f3-5c81-4a20-82e2-5c389d20a2da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_IsPassive
import Theorems.Thm_BosonicLearn_fugacity_isGaussianState
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Theorems.Thm_BosonicLearn_fugacity_photon_number
import Theorems.Thm_BosonicLearn_gammaFock_one_photon
import Theorems.Thm_BosonicLearn_passive_gaussian_fugacity

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open scoped ComplexOrder

open BosonicLearn

/-- Clause 3: the fugacity matrix is read off from the vacuum and one-photon entries of the state. -/
private lemma entry_formula {n : ℕ} (ρ : State (Occupation (Fin n)))
    (R : Matrix (Fin n) (Fin n) ℂ) (hR1 : (1 - R).PosDef)
    (hρ : ρ.coefficients = fugacityCoeff R) (i j : Fin n) :
    R i j = ρ.coefficients (Pi.single i 1) (Pi.single j 1) / ρ.coefficients 0 0 := by
  have hdet : (1 - R).det ≠ 0 := hR1.det_pos.ne'
  obtain ⟨h0, h1⟩ := gammaFock_one_photon R i j
  rw [hρ]
  show R i j = ((1 - R).det • gammaFock R) (Pi.single i 1) (Pi.single j 1) /
    ((1 - R).det • gammaFock R) 0 0
  rw [Matrix.smul_apply, Matrix.smul_apply, h0, h1, smul_eq_mul, smul_eq_mul, mul_one,
    mul_div_cancel_left₀ _ hdet]

theorem solution {n : ℕ} :
    (∀ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef → (1 - R).PosDef →
      ∃ ρ : State (Occupation (Fin n)), ρ.coefficients = fugacityCoeff R ∧ IsPassive ρ) ∧
    (∀ ρ : State (Occupation (Fin n)), IsPassive ρ →
      ∃! R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ (1 - R).PosDef ∧ ρ.coefficients = fugacityCoeff R) ∧
    (∀ (ρ : State (Occupation (Fin n))) (R : Matrix (Fin n) (Fin n) ℂ),
      R.PosSemidef → (1 - R).PosDef → ρ.coefficients = fugacityCoeff R →
      ∀ i j : Fin n, R i j = ρ.coefficients (Pi.single i 1) (Pi.single j 1) / ρ.coefficients 0 0) ∧
    (∀ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef → (1 - R).PosDef →
      ∑' u : Occupation (Fin n), ENNReal.ofReal (∑ i, (u i : ℝ)) * ENNReal.ofReal (fugacityCoeff R u u).re =
        ENNReal.ofReal (R * (1 - R)⁻¹).trace.re) := by
  refine ⟨fun R hR hR1 => ?_, fun ρ hρ => ?_, fun ρ R _ hR1 hρ i j => entry_formula ρ R hR1 hρ i j,
    fun R hR hR1 => fugacity_photon_number R hR hR1⟩
  · -- Clause 1: `det(1 - R) Γ(R)` is a Gaussian state, block diagonal in the photon number.
    obtain ⟨ρ, hρ, hG⟩ := fugacity_isGaussianState R hR hR1
    refine ⟨ρ, hρ, ⟨0, _, hG⟩, fun u v huv => ?_⟩
    rw [hρ]
    show (1 - R).det • gammaFock R u v = 0
    rw [(gammaFock_basic R u v).1 huv, smul_zero]
  · -- Clause 2: existence is `passive_gaussian_fugacity`; uniqueness follows from clause 3.
    obtain ⟨R, hR, hR1, hRρ⟩ := passive_gaussian_fugacity ρ hρ
    refine ⟨R, ⟨hR, hR1, hRρ⟩, fun R' hR' => ?_⟩
    obtain ⟨-, hR1', hRρ'⟩ := hR'
    ext i j
    rw [entry_formula ρ R' hR1' hRρ' i j, entry_formula ρ R hR1 hRρ i j]
