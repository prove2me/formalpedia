-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_original_future_kernel_past_test
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:24:53.521909+00:00
-- url     : https://prove2.me/submissions/a0690ee6-f05a-489b-9b81-c3ec8d6131f9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The source-P full-path Markov factorisation remains true after multiplication
by an arbitrary event measurable with respect to the original stopped history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → E)
    (hH : Measurable[𝓕 s] H)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (f : E × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, (if ω ∈ A then
        f (H ω, fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
      else (0 : ℝ≥0∞)) ∂P) =
    (∫⁻ ω, (if ω ∈ A then
        ∫⁻ y, f (H ω, y)
          ∂(Measure.map (fun ζ => (fun t : ℝ≥0 => X.X t ζ)) P)
      else (0 : ℝ≥0∞)) ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : Ω → (ℝ≥0 → ℝ) := fun ζ t => X.X t ζ
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (s + t) ω - X.X s ω
  let M : Measure (ℝ≥0 → ℝ) := Measure.map Z P
  let Hb : Ω → E × Bool := fun ω => (H ω, decide (ω ∈ A))
  let g : (E × Bool) × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun z => if z.1.2 then f (z.1.1, z.2) else 0
  let J : E × Bool → ℝ≥0∞ := fun h => ∫⁻ y, g (h, y) ∂M
  have hB : Measurable[𝓕 s] (fun ω : Ω => decide (ω ∈ A)) :=
    Measurable.ite hA measurable_const measurable_const
  have hHb : Measurable[𝓕 s] Hb := hH.prodMk hB
  have hHb0 : Measurable Hb := hHb.mono (𝓕.le s) le_rfl
  have hFlag : MeasurableSet {z : (E × Bool) × (ℝ≥0 → ℝ) |
      z.1.2 = true} :=
    (measurableSet_singleton true).preimage (measurable_fst.snd)
  have hF : Measurable
      (fun z : (E × Bool) × (ℝ≥0 → ℝ) => f (z.1.1, z.2)) :=
    hf.comp (measurable_fst.fst.prodMk measurable_snd)
  have hg : Measurable g := Measurable.ite hFlag hF measurable_const
  have hJ : Measurable J := Measurable.lintegral_prod_right' hg
  have hMarkov :=
    chat04_unconditional_history_future_path_markov_tonelli
      X s Hb hHb g hg
  change (∫⁻ ω, g (Hb ω, Y ω) ∂P) =
    ∫⁻ h, J h ∂(Measure.map Hb P) at hMarkov
  calc
    (∫⁻ ω, (if ω ∈ A then f (H ω, Y ω) else 0) ∂P) =
        ∫⁻ ω, g (Hb ω, Y ω) ∂P := by
      apply lintegral_congr
      intro ω
      by_cases hw : ω ∈ A
      · simp [Hb, g, hw]
      · simp [Hb, g, hw]
    _ = ∫⁻ h, J h ∂(Measure.map Hb P) := hMarkov
    _ = ∫⁻ ω, J (Hb ω) ∂P :=
      lintegral_map hJ hHb0
    _ = ∫⁻ ω, (if ω ∈ A then ∫⁻ y, f (H ω, y) ∂M else 0) ∂P := by
      apply lintegral_congr
      intro ω
      by_cases hw : ω ∈ A
      · simp [J, Hb, g, hw]
      · simp [J, Hb, g, hw]
