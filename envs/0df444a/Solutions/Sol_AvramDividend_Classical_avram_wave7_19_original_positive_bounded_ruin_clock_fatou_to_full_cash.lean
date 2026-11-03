-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_positive_bounded_ruin_clock_fatou_to_full_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:21:52.159387+00:00
-- url     : https://prove2.me/submissions/ede28b00-ad12-4c06-bee2-e44727753f2d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- Bounds at every positive bounded ruin clock pass to the original strict-ruin cash support. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hStrategy : IsDividendStrategy 𝓕 D)
    (budget : ℝ≥0∞)
    (hBudget : ∀ n : ℕ, 0 < n →
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget := by
  let I : ℕ → Ω → Set ℝ := fun n ω =>
    paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T
  have hτ : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hStrategy
  have hJointI : ∀ n : ℕ,
      MeasurableSet {p : ℝ × Ω | p.1 ∈ I n p.2} := by
    intro n
    have hMin : Measurable (fun ω => min (ruinTime X x D ω) (n : ℝ≥0∞)) :=
      hτ.min measurable_const
    have hPay := paymentTimes_joint_measurable
      (fun ω => min (ruinTime X x D ω) (n : ℝ≥0∞)) hMin
    have hTime : MeasurableSet {p : ℝ × Ω | p.1 ≤ T} :=
      measurable_fst measurableSet_Iic
    exact hPay.inter hTime
  have hI : ∀ n ω, MeasurableSet (I n ω) := by
    intro n ω
    exact (measurable_id.prodMk measurable_const) (hJointI n)
  have hB : ∀ ω : Ω, MeasurableSet (∅ : Set ℝ) := by
    intro ω
    exact MeasurableSet.empty
  have hJoint : ∀ n : ℕ,
      MeasurableSet {p : ℝ × Ω | p.1 ∈ (∅ : Set ℝ) ∪ I n p.2} := by
    intro n
    simpa only [Set.empty_union] using hJointI n
  have hEv : ∀ᵐ ω ∂P,
      ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ∀ᶠ n : ℕ in Filter.atTop, t ∈ (∅ : Set ℝ) ∪ I n ω := by
    apply Filter.Eventually.of_forall
    intro ω t ht
    have hfinite : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfinite
    have hLarge : ∀ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal t < (n : ℝ≥0∞) := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hNat : (N : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
      exact lt_of_lt_of_le hN hNat
    filter_upwards [hLarge] with n hn
    have hpay : t ∈ paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) := by
      have horiginal : 0 ≤ t ∧
          (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω) := ht.1
      rcases horiginal with ⟨ht0, hz | hpre⟩
      · exact ⟨ht0, Or.inl hz⟩
      · exact ⟨ht0, Or.inr (lt_min hpre hn)⟩
    exact Or.inr ⟨hpay, ht.2⟩
  have hliminf : Filter.liminf (fun n : ℕ =>
      ∫⁻ ω, ∫⁻ t in I n ω,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
      Filter.atTop ≤ budget := by
    have he : ∀ᶠ n : ℕ in Filter.atTop,
        (∫⁻ ω, ∫⁻ t in I n ω,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
      exact hBudget n hn
    have h := Filter.liminf_le_liminf he
    simpa only [Filter.liminf_const] using h
  exact avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
    X q x T D hStrategy (fun _ => ∅) I hB hI hJoint hEv budget (by simpa only [Set.empty_union] using hliminf)
