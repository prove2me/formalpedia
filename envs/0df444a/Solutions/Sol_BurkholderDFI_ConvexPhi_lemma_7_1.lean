-- Prove2me | solution 1 for BurkholderDFI.ConvexPhi.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:11:01.399125+00:00
-- url     : https://prove2.me/submissions/4e59b111-efdd-429f-8034-69d1437e2bc4

import Theorems.Thm_BurkholderDFI_Brownian_lemma_7_1

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
open BurkholderDFI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Lemma 7.1, p. 26: the good-λ lemma. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (β δ ε : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hε : 0 < ε)
    (h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < g ω})
    (γ η : ℝ≥0)
    (h72 : ∀ l : ℝ, 0 < l →
      Φ (ENNReal.ofReal (β * l)) ≤ γ * Φ (ENNReal.ofReal l) ∧
      Φ (ENNReal.ofReal (δ⁻¹ * l)) ≤ η * Φ (ENNReal.ofReal l))
    (hγε : (γ : ℝ) * ε < 1) :
    ∫⁻ ω, Φ (g ω) ∂P ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * ∫⁻ ω, Φ (f ω) ∂P :=
  BurkholderDFI.Brownian.lemma_7_1 P Φ c hΦ f g hf hg β δ ε hβ hδ hε h71 γ η h72 hγε