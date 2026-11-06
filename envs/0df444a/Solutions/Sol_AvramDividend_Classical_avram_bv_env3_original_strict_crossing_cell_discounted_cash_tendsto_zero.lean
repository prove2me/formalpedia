-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:09:16.744555+00:00
-- url     : https://prove2.me/submissions/b1d829a3-b2c5-4f8b-a749-3d5f1539e516

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The strict final original-process crossing cell loses all mass in the limit.
    Its horizon singleton is deliberately excluded from this statement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Monotone a)
    (hlim : Tendsto a atTop (nhds (T : ℝ))) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioo (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let S : ℕ → Set ℝ := fun n => paymentTimes σ ∩ Ioo (a n) (T : ℝ)
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let g : ℕ → ℝ → ℝ≥0∞ := fun n t => (S n).indicator f t
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    (avram_p4_d_dividend_original_paymentTimes_measurableSet σ).inter isOpen_Ioo.measurableSet
  have hfm : Measurable f := by fun_prop
  have hgm (n : ℕ) : Measurable (g n) := hfm.indicator (hSm n)
  have hanti (t : ℝ) : Antitone (fun n => g n t) := by
    intro i j hij
    have hsubset : S j ⊆ S i := by
      intro u hu
      exact ⟨hu.1, ⟨lt_of_le_of_lt (ha hij) hu.2.1, hu.2.2⟩⟩
    by_cases hj : t ∈ S j
    · have hi : t ∈ S i := hsubset hj
      simp [g, hj, hi]
    · by_cases hi : t ∈ S i
      · simp [g, hj, hi]
      · simp [g, hj, hi]
  have hpoint (t : ℝ) : Tendsto (fun n => g n t) atTop (nhds 0) := by
    by_cases ht : t < (T : ℝ)
    · have hevent : ∀ᶠ n in atTop, t < a n :=
        hlim.eventually (isOpen_Ioi.mem_nhds ht)
      have heq : (fun n => g n t) =ᶠ[atTop] (fun _ => (0 : ℝ≥0∞)) := by
        filter_upwards [hevent] with n hn
        have hnot : t ∉ S n := by
          intro hmem
          exact (not_lt_of_ge (le_of_lt hn)) hmem.2.1
        simp [g, hnot]
      exact tendsto_const_nhds.congr' heq.symm
    · have hnot (n : ℕ) : t ∉ S n := by
        intro hmem
        exact ht hmem.2.2
      have heq : (fun n => g n t) = (fun _ => (0 : ℝ≥0∞)) := by
        funext n
        simp [g, hnot n]
      rw [heq]
      exact tendsto_const_nhds
  have hfinite : (∫⁻ t, g 0 t ∂μ) ≠ ⊤ := by
    have hsubset : S 0 ⊆ paymentTimes σ ∩ Iic (T : ℝ) := by
      intro t ht
      exact ⟨ht.1, le_of_lt ht.2.2⟩
    have hle := lintegral_mono_set (f := f) (μ := μ) hsubset
    have hbound : (∫⁻ t in S 0, f t ∂μ) < ⊤ :=
      lt_of_le_of_lt hle
        (avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
          D hD ω σ T q hq)
    rw [lintegral_indicator (hSm 0) f]
    exact ne_of_lt hbound
  have hlimint : Tendsto (fun n => ∫⁻ t, g n t ∂μ) atTop (nhds 0) := by
    simpa using (lintegral_tendsto_of_tendsto_of_antitone
      (fun n => (hgm n).aemeasurable) (Filter.Eventually.of_forall hanti)
      hfinite (Filter.Eventually.of_forall hpoint))
  have heq (n : ℕ) : (∫⁻ t, g n t ∂μ) = (∫⁻ t in S n, f t ∂μ) :=
    lintegral_indicator (hSm n) f
  simpa [S, f, μ] using hlimint.congr' (Filter.Eventually.of_forall heq)
