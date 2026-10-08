-- Prove2me | solution 1 for AvramDividend.Classical.truncated_dividend_path_value_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:38:40.88598+00:00
-- url     : https://prove2.me/submissions/b7d5dc51-31d7-4fc9-b243-b254970fa2a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_restrict_Ioc_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_lintegral_kernel_prod_right_of_pointwise_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) (n : ℕ) :
    AEMeasurable
      (fun ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) P := by
  let B : Set ℝ := Ioc (-1 : ℝ) (n : ℝ)
  let μ : Ω → Measure ℝ :=
    fun ω => (dividendMeasure D ω).restrict B
  have hμ : Measurable μ := by
    dsimp [μ, B]
    exact dividendMeasure_restrict_Ioc_measurable
      D hD.1 (-1 : ℝ) (n : ℝ)
  let κ : Kernel Ω ℝ := ⟨μ, hμ⟩
  have hκfin : ∀ ω, IsFiniteMeasure (κ ω) := by
    intro ω
    change IsFiniteMeasure ((dividendMeasure D ω).restrict B)
    rw [MeasureTheory.isFiniteMeasure_restrict]
    have hmono : Monotone (fun r : ℝ => D r.toNNReal ω) :=
      (hD.1.2.1 ω).comp Real.toNNReal_monotone
    dsimp [B]
    unfold dividendMeasure
    rw [dif_pos hmono, StieltjesFunction.measure_Ioc,
      Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq]
    exact ENNReal.ofReal_ne_top
  let S : Set (Ω × ℝ) :=
    {p | p.2 ∈ paymentTimes (ruinTime X x D p.1) ∩ Iic (n : ℝ)}
  have hS : MeasurableSet S := by
    have hτ :
        Measurable (fun p : Ω × ℝ => ruinTime X x D p.1) :=
      (ruinTime_measurable X x D hD.1).comp measurable_fst
    have ht : Measurable (fun p : Ω × ℝ => p.2) := measurable_snd
    have hof :
        Measurable (fun p : Ω × ℝ => ENNReal.ofReal p.2) :=
      ENNReal.measurable_ofReal.comp ht
    have hnonneg : MeasurableSet {p : Ω × ℝ | 0 ≤ p.2} :=
      measurableSet_le measurable_const ht
    have hzero : MeasurableSet {p : Ω × ℝ | p.2 = 0} :=
      measurableSet_eq_fun ht measurable_const
    have hbefore :
        MeasurableSet
          {p : Ω × ℝ | ENNReal.ofReal p.2 < ruinTime X x D p.1} :=
      measurableSet_lt hof hτ
    have hn : MeasurableSet {p : Ω × ℝ | p.2 ≤ (n : ℝ)} :=
      measurableSet_le ht measurable_const
    have hpay :
        MeasurableSet
          {p : Ω × ℝ |
            0 ≤ p.2 ∧
              (p.2 = 0 ∨ ENNReal.ofReal p.2 < ruinTime X x D p.1)} :=
      hnonneg.inter (hzero.union hbefore)
    have hcap :
        MeasurableSet
          {p : Ω × ℝ |
            (0 ≤ p.2 ∧
              (p.2 = 0 ∨ ENNReal.ofReal p.2 < ruinTime X x D p.1)) ∧
              p.2 ≤ (n : ℝ)} :=
      hpay.inter hn
    dsimp [S]
    unfold paymentTimes
    change MeasurableSet
      {p : Ω × ℝ |
        (0 ≤ p.2 ∧
          (p.2 = 0 ∨ ENNReal.ofReal p.2 < ruinTime X x D p.1)) ∧
          p.2 ≤ (n : ℝ)}
    exact hcap
  let g : Ω × ℝ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp (-(q * p.2)))
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  let F : Ω × ℝ → ℝ≥0∞ := S.indicator g
  have hF : Measurable F := by
    exact hg.indicator hS
  have hInt :
      Measurable (fun ω => ∫⁻ t, F (ω, t) ∂κ ω) :=
    measurable_lintegral_kernel_prod_right_of_pointwise_finite
      κ hκfin hF
  have heq :
      (fun ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (fun ω => ∫⁻ t, F (ω, t) ∂κ ω) := by
    funext ω
    let A : Set ℝ :=
      paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)
    have hA : MeasurableSet A := by
      dsimp [A]
      unfold paymentTimes
      measurability
    have hAB : A ⊆ B := by
      intro t htA
      have ht0 : 0 ≤ t := htA.1.1
      have htn : t ≤ (n : ℝ) := htA.2
      exact ⟨by linarith, htn⟩
    dsimp [F, S, g, κ, μ]
    change
      (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) =
      ∫⁻ t, A.indicator
        (fun t => ENNReal.ofReal (Real.exp (-(q * t)))) t
        ∂((dividendMeasure D ω).restrict B)
    rw [lintegral_indicator hA]
    change
      (∫⁻ t, ENNReal.ofReal (Real.exp (-(q * t)))
        ∂((dividendMeasure D ω).restrict A)) =
      ∫⁻ t, ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(((dividendMeasure D ω).restrict B).restrict A)
    rw [Measure.restrict_restrict_of_subset hAB]
  rw [heq]
  exact hInt.aemeasurable
