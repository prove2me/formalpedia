-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:04:00.630056+00:00
-- url     : https://prove2.me/submissions/548c03d3-2385-4d8c-88d8-0e37dc40c2a6

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Monotone convergence of the actual original discounted dividend measure
at cofinal strict cutoffs, retaining diffuse and right-atomic payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n)
    (hMeas : ∀ n, MeasurableSet
      (paymentTimes (ruinTime X x D ω) ∩ Iio (u n))) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) =
      ⨆ n, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by
  let E : ℕ → Set ℝ := fun n => paymentTimes (ruinTime X x D ω) ∩ Iio (u n)
  let F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hEmeas (n : ℕ) : MeasurableSet (E n) := hMeas n
  have hEmono : Monotone E := by
    intro n m hnm t ht; exact ⟨ht.1, lt_of_lt_of_le ht.2 (hmono hnm)⟩
  have hUnion : (⋃ n, E n) = paymentTimes (ruinTime X x D ω) ∩ Iio T := by
    ext t
    simp only [E, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iio]
    constructor
    · rintro ⟨n, hp, ht⟩
      exact ⟨hp, lt_of_lt_of_le ht (hbelow n)⟩
    · rintro ⟨hp, ht⟩
      obtain ⟨n, hn⟩ := hcover t ht; exact ⟨n, hp, hn⟩
  have hEU : MeasurableSet (⋃ n, E n) := MeasurableSet.iUnion hEmeas
  have hFmeas : Measurable F := by dsimp [F]; fun_prop
  have hIndicators (n : ℕ) : Measurable ((E n).indicator F) :=
    hFmeas.indicator (hEmeas n)
  have hImono : Monotone (fun n => (E n).indicator F) := by
    intro n m hnm t
    change (E n).indicator F t ≤ (E m).indicator F t
    by_cases ht : t ∈ E n
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hEmono hnm ht)]
    · rw [Set.indicator_of_notMem ht]; exact bot_le
  have hPoint (t : ℝ) :
      (⋃ n, E n).indicator F t = ⨆ n, (E n).indicator F t := by
    by_cases ht : t ∈ ⋃ n, E n
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
      rw [Set.indicator_of_mem ht]
      apply le_antisymm
      · have hN : (E n).indicator F t = F t := by
          simp [Set.indicator_of_mem hn]
        rw [← hN]
        exact le_iSup (fun m : ℕ => (E m).indicator F t) n
      · apply iSup_le; intro m
        by_cases hm : t ∈ E m
        · simp [Set.indicator_of_mem hm]
        · simp [Set.indicator_of_notMem hm]
    · rw [Set.indicator_of_notMem ht]
      apply le_antisymm
      · exact bot_le
      · apply iSup_le; intro n
        have hn : t ∉ E n := fun h => ht (Set.mem_iUnion.mpr ⟨n, h⟩)
        simp [Set.indicator_of_notMem hn]
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T, F t ∂dividendMeasure D ω) =
        (∫⁻ t, (⋃ n, E n).indicator F t ∂dividendMeasure D ω) := by
          rw [← hUnion]
          exact (lintegral_indicator hEU F).symm
    _ = (∫⁻ t, ⨆ n, (E n).indicator F t ∂dividendMeasure D ω) := by
          congr 1; funext t; exact hPoint t
    _ = ⨆ n, (∫⁻ t, (E n).indicator F t ∂dividendMeasure D ω) :=
          lintegral_iSup hIndicators hImono
    _ = ⨆ n, (∫⁻ t in E n, F t ∂dividendMeasure D ω) := by
          congr 1; funext n; exact lintegral_indicator (hEmeas n) F
