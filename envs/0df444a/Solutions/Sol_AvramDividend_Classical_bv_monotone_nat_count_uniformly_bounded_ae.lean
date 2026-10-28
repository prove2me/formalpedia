-- Prove2me | solution 1 for AvramDividend.Classical.bv_monotone_nat_count_uniformly_bounded_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:37:24.705697+00:00
-- url     : https://prove2.me/submissions/78659b8a-9408-46dd-a91f-26520596f4e5

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-- Uniform bounds on expected nondecreasing natural counts yield a finite count ceiling a.s. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℕ) (C : ℝ≥0∞)
    (hF : ∀ n, Measurable (fun ω => (F n ω : ℝ≥0∞)))
    (hMono : Monotone (fun n => fun ω => (F n ω : ℝ≥0∞)))
    (hBound : ∀ n, (∫⁻ ω, (F n ω : ℝ≥0∞) ∂P) ≤ C)
    (hFinite : C < ⊤) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ n : ℕ, F n ω ≤ K := by
  have hInt : (∫⁻ ω, ⨆ n, (F n ω : ℝ≥0∞) ∂P) ≤ C := by
    rw [lintegral_iSup hF hMono]
    exact iSup_le hBound
  have hA : ∀ᵐ ω ∂P, (⨆ n, (F n ω : ℝ≥0∞)) < ⊤ :=
    ae_lt_top (Measurable.iSup hF) (lt_of_le_of_lt hInt hFinite).ne
  filter_upwards [hA] with ω hω
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt hω.ne
  refine ⟨K, fun n => ?_⟩
  have hn : (F n ω : ℝ≥0∞) ≤ (K : ℝ≥0∞) :=
    (le_iSup (fun n => (F n ω : ℝ≥0∞)) n).trans hK.le
  exact_mod_cast hn
