-- Prove2me | solution 1 for AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T03:29:16.466015+00:00
-- url     : https://prove2.me/submissions/950bd3cf-4681-4035-97c7-c9980b4cef75
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_countable_rightJump_concentration
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable
import Theorems.Thm_AvramDividend_Classical_local_verification_separated_countable_dividend_budget
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The expected discounted dividends paid before ruin and up to the horizon
`T` are bounded by the initial verification value `w x`; see the
companion file for the route. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hperω : ∀ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (w x) := by
    intro ω
    classical
    set μ : Measure ℝ := dividendMeasure D ω with hμ
    set S : Set ℝ :=
      {t : ℝ | 0 ≤ t ∧ rightLimit D t.toNNReal ω ≠ D t.toNNReal ω} with hSdef
    set A : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic T with hAdef
    -- The right-jump support is countable, and the measure is carried by it.
    have hScount : S.Countable :=
      dividendStrategy_rightJump_support_countable D hD.1.1 ω
    have hconc : μ.restrict S = μ :=
      dividendMeasure_countable_rightJump_concentration (P := P) D hD.1.1 ω S hSdef
    -- The payment times in `A ∩ S` are nonneg and precede ruin.
    have hAS : A ∩ S ⊆ paymentTimes (ruinTime X x D ω) ∩ Iic T := by
      intro t ht
      exact ht.1
    have hNonneg : ∀ s ∈ A ∩ S, 0 ≤ s := by
      intro s hs
      exact (hAS hs).1.1
    have hActive : ∀ s ∈ A ∩ S,
        s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
      intro s hs
      have hs' := hAS hs
      have hsact := paymentTimes_membership_to_nNReal_active
        (ruinTime X x D ω) s hs'.1
      exact hsact.2
    have hcount :
        (∫⁻ s in A ∩ S,
          ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
        ENNReal.ofReal (w x) := by
      have hAScount : (A ∩ S).Countable :=
        hScount.mono Set.inter_subset_right
      have hbound :=
        local_verification_separated_countable_dividend_budget
          X x q w C hw_cont
          (⟨fun hnot => absurd hBV hnot, fun _ => hw_smooth⟩)
          hw_gen hw_grad D hD hxc ω (A ∩ S) hAScount hNonneg hActive
      simpa only [hμ] using hbound
    have hAmeasurable : MeasurableSet A := by
      rw [hAdef]
      exact MeasurableSet.inter (paymentTimes_measurable (ruinTime X x D ω)) measurableSet_Iic
    have hASmeasurable : MeasurableSet (A ∩ S) :=
      MeasurableSet.inter hAmeasurable hScount.measurableSet
    have hrestrict : μ.restrict A = μ.restrict (A ∩ S) := by
      have hstep : (μ.restrict S).restrict A = μ.restrict (A ∩ S) :=
        Measure.restrict_restrict' (s := A) (t := S) hScount.measurableSet
      calc
        μ.restrict A = (μ.restrict univ).restrict A := by rw [Measure.restrict_univ]
        _ = (μ.restrict S).restrict A := by
          rw [Measure.restrict_univ]
          exact congrArg (fun m : Measure ℝ => m.restrict A) hconc.symm
        _ = μ.restrict (A ∩ S) := hstep
    have hsplit :
        (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
        (∫⁻ t in A ∩ S, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := by
      rw [← lintegral_indicator hAmeasurable, ← lintegral_indicator hASmeasurable]
      have hset : (A.indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))) =ᵐ[μ]
          ((A ∩ S).indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))) := by
        have hzero : μ {t | t ∈ A ∧ t ∉ S} = 0 := by
          have hμSc : μ (Set.univ \ S) = 0 := by
            rw [← hconc, Measure.restrict_apply' hScount.measurableSet]; simp
          have hsub : {t | t ∈ A ∧ t ∉ S} ⊆ Set.univ \ S := fun u hu => ⟨Set.mem_univ u, hu.2⟩
          have hle : μ {t | t ∈ A ∧ t ∉ S} ≤ μ (Set.univ \ S) := MeasureTheory.Measure.measure_mono_both (le_refl μ) hsub
          exact le_antisymm (hle.trans hμSc.le) (bot_le)
        show ∀ᵐ a ∂μ,
          A.indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) a =
            (A ∩ S).indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) a
        rw [MeasureTheory.ae_iff]
        have hsub : {a | A.indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) a ≠
              (A ∩ S).indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) a} ⊆
            {t | t ∈ A ∧ t ∉ S} := by
          intro u hu
          by_cases huA : u ∈ A
          · by_cases huS : u ∈ S
            · exact absurd hu (by simp [huA, huS])
            · exact ⟨huA, huS⟩
          · exact absurd (by simp [huA]) hu
        have hle : μ {a | A.indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) a ≠
              (A ∩ S).indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) a} ≤
            μ {t | t ∈ A ∧ t ∉ S} := MeasureTheory.Measure.measure_mono_both (le_refl μ) hsub
        exact le_antisymm (hle.trans hzero.le) (bot_le)
      exact MeasureTheory.lintegral_congr_ae hset
    rw [hsplit]
    exact hcount
  have hmono : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (w x) := by
    filter_upwards [] with ω
    exact hperω ω
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ∫⁻ _ : Ω, ENNReal.ofReal (w x) ∂P :=
      lintegral_mono_ae hmono
    _ = ENNReal.ofReal (w x) := by
      rw [lintegral_const]
      have hpuniv : P Set.univ = 1 := X.isProbability.measure_univ
      rw [hpuniv]
      simp

