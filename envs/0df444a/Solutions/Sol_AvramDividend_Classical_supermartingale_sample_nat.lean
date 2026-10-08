-- Prove2me | solution 1 for AvramDividend.Classical.supermartingale_sample_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:50:26.50827+00:00
-- url     : https://prove2.me/submissions/16f06553-dbfd-4ed5-919a-fa5301f9b728

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Supermartingale f 𝓕 μ) :
    Supermartingale (fun n : ℕ => f (n : ℝ≥0)) 𝓖 μ := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change StronglyMeasurable[𝓖 n] (f (n : ℝ≥0))
    rw [h𝓖 n]
    exact hf.1 (n : ℝ≥0)
  · intro n m hnm
    have hnm' : (n : ℝ≥0) ≤ (m : ℝ≥0) := by exact_mod_cast hnm
    change μ[f (m : ℝ≥0) | 𝓖 n] ≤ᵐ[μ] f (n : ℝ≥0)
    rw [h𝓖 n]
    exact hf.2.1 (n : ℝ≥0) (m : ℝ≥0) hnm'
  · intro n
    change Integrable (f (n : ℝ≥0)) μ
    exact hf.2.2 (n : ℝ≥0)
