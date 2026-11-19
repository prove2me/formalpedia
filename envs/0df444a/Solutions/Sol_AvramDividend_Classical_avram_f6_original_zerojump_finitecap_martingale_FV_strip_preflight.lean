-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_zerojump_finitecap_martingale_FV_strip_preflight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:37:00.889339+00:00
-- url     : https://prove2.me/submissions/704a6616-04eb-4bd3-af9c-0d170ae5d530

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_admissible_upperstrip_expected_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    Martingale (fun t ω => X.X t ω - (t : ℝ) * X.c)
      𝓕.rightCont P ∧
    Martingale (fun t ω =>
      (X.X t ω - (t : ℝ) * X.c) ^ 2 -
        (t : ℝ) * X.σ ^ 2) 𝓕.rightCont P ∧
    (∀ ω, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => rightLimit D t ω) Set.univ) ∧
    (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X.X t ω)) ∧
    (∀ t ω, x + X.X t ω - rightLimit D t ω =
      (X.X t ω - (t : ℝ) * X.c) +
        (x + (t : ℝ) * X.c - rightLimit D t ω)) ∧
    Tendsto (fun j : ℕ =>
      ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨hM, hQ, hFV, hContinuous, hDecomp⟩ :=
    avram_gbB199_original_zerojump_gaussian_FV_semimartingale_preflight
      X hν x D hD.1.1
  have hOcc :=
    avram_f6_original_finitecap_admissible_upperstrip_expected_zero
      X hBV x C hC hFinite hxc D hD n hn
  exact ⟨hM, hQ, hFV, hContinuous, hDecomp, hOcc⟩
