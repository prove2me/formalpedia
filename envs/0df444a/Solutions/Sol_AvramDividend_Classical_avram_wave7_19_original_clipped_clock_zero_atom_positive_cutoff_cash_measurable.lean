-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_clipped_clock_zero_atom_positive_cutoff_cash_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:50:23.751965+00:00
-- url     : https://prove2.me/submissions/ba3947dd-2215-4741-8a55-c4cd9b50154f



import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n k : ℕ) :
    Measurable (fun ω : Ω =>
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  classical
  obtain ⟨κ, hκ, heq⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hκ
  let τ : Ω → ℝ≥0∞ := fun ω => min (ruinTime X x D ω) (n : ℝ≥0∞)
  have hτ : Measurable τ := by
    exact (ruinTime_measurable X x D hD).min measurable_const
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hf : Measurable f := by dsimp [f]; fun_prop
  let a : ℝ := 1 / ((k : ℝ) + 1)
  let S0 : Set (ℝ × Ω) := {p | p.1 = 0}
  let Spos : Set (ℝ × Ω) := {p | p.1 ∈ paymentTimes (τ p.2) ∩ Icc a T}
  have hS0 : MeasurableSet S0 := by
    change MeasurableSet ((fun p : ℝ × Ω => p.1) ⁻¹' ({0} : Set ℝ))
    exact (measurableSet_singleton 0).preimage measurable_fst
  have hSI : MeasurableSet {p : ℝ × Ω | p.1 ∈ Icc a T} :=
    measurableSet_Icc.preimage measurable_fst
  have hSpos : MeasurableSet Spos := by
    have hEq : Spos =
        {p : ℝ × Ω | p.1 ∈ paymentTimes (τ p.2)} ∩
        {p : ℝ × Ω | p.1 ∈ Icc a T} := by
      ext p; simp only [Spos, mem_setOf_eq, mem_inter_iff]
    rw [hEq]
    exact (paymentTimes_joint_measurable τ hτ).inter hSI
  have h0 : Measurable (fun ω : Ω =>
      ∫⁻ t in ({0} : Set ℝ), f t ∂(dividendMeasure D ω)) := by
    have hK := measurable_random_indicator_lintegral κ S0 hS0 f hf
    have hEq : (fun ω : Ω =>
        ∫⁻ t in ({0} : Set ℝ), f t ∂(dividendMeasure D ω)) =
        (fun ω : Ω => ∫⁻ t, if (t, ω) ∈ S0 then f t else 0 ∂κ ω) := by
      funext ω
      rw [← heq ω]
      change (∫⁻ t in ({0} : Set ℝ), f t ∂κ ω) =
        ∫⁻ t, ({0} : Set ℝ).indicator f t ∂κ ω
      exact (lintegral_indicator (measurableSet_singleton 0) f).symm
    rw [hEq]; exact hK
  have hpos : Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (τ ω) ∩ Icc a T,
        f t ∂(dividendMeasure D ω)) := by
    have hK := measurable_random_indicator_lintegral κ Spos hSpos f hf
    convert hK using 1
    funext ω
    rw [← heq ω]
    have hA : MeasurableSet (paymentTimes (τ ω) ∩ Icc a T) := by
      dsimp [paymentTimes]; measurability
    calc
      (∫⁻ t in paymentTimes (τ ω) ∩ Icc a T, f t ∂κ ω) =
          ∫⁻ t, (paymentTimes (τ ω) ∩ Icc a T).indicator f t ∂κ ω :=
        (lintegral_indicator hA f).symm
      _ = ∫⁻ t, if (t, ω) ∈ Spos then f t else 0 ∂κ ω := by
        apply lintegral_congr
        intro t
        by_cases ht : t ∈ paymentTimes (τ ω) ∩ Icc a T
        · have hs : (t, ω) ∈ Spos := ht
          simp only [Set.indicator, if_pos ht, if_pos hs]
        · have hs : (t, ω) ∉ Spos := ht
          simp only [Set.indicator, if_neg ht, if_neg hs]
    all_goals
      apply lintegral_congr
      intro t
      by_cases hs : (t, ω) ∈ Spos
      · simp only [if_pos hs]
      · simp only [if_neg hs]
  change Measurable (fun ω : Ω =>
    (∫⁻ t in ({0} : Set ℝ), f t ∂(dividendMeasure D ω)) +
    (∫⁻ t in paymentTimes (τ ω) ∩ Icc a T,
      f t ∂(dividendMeasure D ω)))
  exact h0.add hpos
