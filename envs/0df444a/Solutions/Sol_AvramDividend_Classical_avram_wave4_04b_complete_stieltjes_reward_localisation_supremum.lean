-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_complete_stieltjes_reward_localisation_supremum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:00:52.423971+00:00
-- url     : https://prove2.me/submissions/17d4a044-d15a-4f92-9e94-8154e9e000a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_payment_times_supremum_clock_union
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Full source Stieltjes mass, including right atoms and singular-continuous
variation, is continuous along increasing stopping-clock localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (τ : ℕ → ℝ≥0∞) (hτ : Monotone τ)
    (v : ℝ → ℝ≥0∞) (hv : Measurable v) :
    (∫⁻ s in paymentTimes (⨆ n, τ n) ∩ Iic (T : ℝ),
      v s ∂dividendMeasure D ω) =
    ⨆ n, (∫⁻ s in paymentTimes (τ n) ∩ Iic (T : ℝ),
      v s ∂dividendMeasure D ω) := by
  let S : ℕ → Set ℝ := fun n => paymentTimes (τ n) ∩ Iic (T : ℝ)
  let F : ℕ → ℝ → ℝ≥0∞ := fun n s => (S n).indicator v s
  have hPm : ∀ {a b : ℝ≥0∞}, a ≤ b → paymentTimes a ⊆ paymentTimes b := by
    intro a b hab s hs
    change s ∈ Ici (0 : ℝ) ∩ ({0} ∪ {u : ℝ | ENNReal.ofReal u < a}) at hs
    change s ∈ Ici (0 : ℝ) ∩ ({0} ∪ {u : ℝ | ENNReal.ofReal u < b})
    rcases hs with ⟨hs0, hs | hs⟩
    · exact ⟨hs0, Or.inl hs⟩
    · exact ⟨hs0, Or.inr (lt_of_lt_of_le hs hab)⟩
  have hSm : Monotone S := by
    intro n m hnm s hs
    exact ⟨hPm (hτ hnm) hs.1, hs.2⟩
  have hSmeas (n : ℕ) : MeasurableSet (S n) :=
    (paymentTimes_measurable (τ n)).inter measurableSet_Iic
  have hFm (n : ℕ) : Measurable (F n) := hv.indicator (hSmeas n)
  have hFmono : Monotone F := by
    intro n m hnm s
    by_cases hs : s ∈ S n
    · have hs' : s ∈ S m := hSm hnm hs
      simp [F, Set.indicator_of_mem hs, Set.indicator_of_mem hs']
    · simp only [F, Set.indicator_of_notMem hs]; exact bot_le
  have hU : (⋃ n, S n) =
      paymentTimes (⨆ n, τ n) ∩ Iic (T : ℝ) := by
    rw [avram_wave4_04b_payment_times_supremum_clock_union τ]
    ext s
    simp only [S, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨n, hs, hT⟩; exact ⟨⟨n, hs⟩, hT⟩
    · rintro ⟨⟨n, hs⟩, hT⟩; exact ⟨n, hs, hT⟩
  have hSup (s : ℝ) :
      ((⋃ n, S n).indicator v) s = ⨆ n, F n s := by
    apply le_antisymm
    · by_cases hs : s ∈ ⋃ n, S n
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hs
        apply le_iSup_of_le n
        simp only [F, Set.indicator_of_mem hs, Set.indicator_of_mem hn]; exact le_rfl
      · simp only [Set.indicator_of_notMem hs]; exact bot_le
    · apply iSup_le
      intro n
      by_cases hn : s ∈ S n
      · have hs : s ∈ ⋃ k, S k := Set.mem_iUnion.mpr ⟨n, hn⟩
        simp only [F, Set.indicator_of_mem hn, Set.indicator_of_mem hs]; exact le_rfl
      · simp only [F, Set.indicator_of_notMem hn]; exact bot_le
  have hUmeas : MeasurableSet (⋃ n, S n) :=
    MeasurableSet.iUnion hSmeas
  calc
    (∫⁻ s in paymentTimes (⨆ n, τ n) ∩ Iic (T : ℝ),
        v s ∂dividendMeasure D ω) =
      (∫⁻ s : ℝ, (⋃ n, S n).indicator v s ∂dividendMeasure D ω) := by
        rw [← hU]
        exact (lintegral_indicator hUmeas v).symm
    _ = (∫⁻ s : ℝ, ⨆ n, F n s ∂dividendMeasure D ω) :=
      lintegral_congr hSup
    _ = ⨆ n, (∫⁻ s : ℝ, F n s ∂dividendMeasure D ω) :=
      lintegral_iSup hFm hFmono
    _ = ⨆ n, (∫⁻ s in S n, v s ∂dividendMeasure D ω) := by
      congr 1; funext n; exact lintegral_indicator (hSmeas n) v
    _ = _ := rfl
