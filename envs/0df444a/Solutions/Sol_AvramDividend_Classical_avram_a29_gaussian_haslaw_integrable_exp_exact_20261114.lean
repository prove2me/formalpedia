-- Prove2me | solution 1 for AvramDividend.Classical.avram_a29_gaussian_haslaw_integrable_exp_exact_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:16:30.140201+00:00
-- url     : https://prove2.me/submissions/7957a5ea-d95f-4c01-8a08-74d930631618

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Exact exponential integrability and moment generating formula from a centred real Gaussian law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G : Ω → ℝ) (v : ℝ≥0)
    (hLaw : HasLaw G (gaussianReal 0 v) P) :
    ∀ θ : ℝ,
      Integrable (fun ω => Real.exp (θ * G ω)) P ∧
      (∫ ω, Real.exp (θ * G ω) ∂P) =
        Real.exp ((v : ℝ) * θ ^ 2 / 2) := by
  intro θ
  have hInt : Integrable (fun x : ℝ => Real.exp (θ * x))
      (gaussianReal 0 v) :=
    integrable_exp_mul_gaussianReal θ
  have hIntMap : Integrable (fun x : ℝ => Real.exp (θ * x)) (P.map G) := by
    rw [hLaw.map_eq]
    exact hInt
  have hIntG : Integrable (fun ω => Real.exp (θ * G ω)) P :=
    hIntMap.comp_aemeasurable hLaw.aemeasurable
  refine ⟨hIntG, ?_⟩
  simpa [mgf] using (mgf_gaussianReal hLaw.map_eq θ)
