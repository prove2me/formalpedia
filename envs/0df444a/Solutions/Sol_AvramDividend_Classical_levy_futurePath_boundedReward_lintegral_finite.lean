-- Prove2me | solution 1 for AvramDividend.Classical.levy_futurePath_boundedReward_lintegral_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:31:23.362242+00:00
-- url     : https://prove2.me/submissions/6607c9f5-535d-433a-8aef-255867c3f9af

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A path reward dominated by an integrable constant has finite Lévy path-law mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) ≠ ∞ := by
  let path : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X t ω
  have hpath : Measurable path := by
    apply measurable_pi_iff.mpr
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hMass : (Measure.map path P) Set.univ = P Set.univ := by
    simp [Measure.map_apply hpath MeasurableSet.univ]
  have hle : (∫⁻ y, g y ∂(Measure.map path P)) ≤
      C * P Set.univ := by
    calc
      _ ≤ ∫⁻ y, C ∂(Measure.map path P) :=
        lintegral_mono hbound
      _ = C * (Measure.map path P) Set.univ := by
        simp only [lintegral_const]
      _ = C * P Set.univ := by rw [hMass]
  have hf : C * P Set.univ ≠ ∞ := by
    simpa only [lintegral_const] using hfin
  intro ht
  have htop : (⊤ : ℝ≥0∞) ≤ C * P Set.univ := by
    calc
      (⊤ : ℝ≥0∞) =
          (∫⁻ y, g y ∂(Measure.map path P)) := ht.symm
      _ ≤ _ := hle
  exact hf (top_le_iff.mp htop)
