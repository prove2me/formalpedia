-- Prove2me | solution 3 for AvramDividend.Classical.local_verification_separated_countable_dividend_budget
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T09:43:14.409901+00:00
-- url     : https://prove2.me/submissions/450a8fa9-2b41-43f6-97aa-e03d8e883516

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

open ProbabilityTheory Function

private noncomputable def zeroFiltration :
    Filtration ℝ≥0 (⊤ : MeasurableSpace PUnit) where
  seq _ := ⊤
  mono' _ _ _ := le_rfl
  le' _ := le_rfl

private lemma nhdsWithin_Iio_neBot_of_pos {t : ℝ≥0} (ht : 0 < t) :
    (𝓝[<] t).NeBot := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  have hne : (Iio t).Nonempty := ⟨0, ht⟩
  rw [closure_Iio' hne]
  exact le_refl t

private noncomputable def zeroLevy :
    SpectrallyNegativeLevy (Measure.dirac PUnit.unit) zeroFiltration where
  X _ _ := 0
  c := 0
  σ := 0
  ν := 0
  isProbability := inferInstance
  σ_nonneg := le_rfl
  ν_Ici := by simp
  ν_integrable := by simp
  X_zero _ := rfl
  rightCont _ _ := continuousWithinAt_const
  leftLim _ _ _ := ⟨0, tendsto_const_nhds⟩
  noPosJumps _ t l ht hl := by
    have : (𝓝[<] t).NeBot := nhdsWithin_Iio_neBot_of_pos ht
    rw [tendsto_nhds_unique hl tendsto_const_nhds]
  adapted _ := measurable_const
  indepIncrements _ _ _ := by
    rw [ProbabilityTheory.Indep_iff]
    intro t₁ t₂ _ _
    have hm1 : MeasurableSet t₁ := trivial
    have hm2 : MeasurableSet t₂ := trivial
    simp [Measure.dirac_apply' _ hm1, Measure.dirac_apply' _ hm2,
      Measure.dirac_apply' _ (hm1.inter hm2), Set.indicator]
    by_cases h1 : PUnit.unit ∈ t₁ <;> by_cases h2 : PUnit.unit ∈ t₂ <;> simp [h1, h2]
  stationaryIncrements _ _ _ := by
    have heq : (fun _ : PUnit => (0 : ℝ) - 0) = (fun _ : PUnit => (0 : ℝ)) := by
      ext
      ring
    rw [heq]
    exact IdentDistrib.refl aemeasurable_const
  laplace _ _ _ := by
    refine ⟨integrable_const _, ?_⟩
    rw [integral_dirac]
    simp [laplaceExponent]

private noncomputable def stepD (t : ℝ≥0) (_ : PUnit) : ℝ :=
  if t = 0 then 0 else 1

private lemma stepD_mono (ω : PUnit) : Monotone (fun t : ℝ≥0 => stepD t ω) := by
  intro a b hab
  simp only [stepD]
  split_ifs with ha hb hb
  · exact le_rfl
  · norm_num
  · exfalso
    exact ha (le_antisymm (hab.trans (le_of_eq hb)) bot_le)
  · exact le_rfl

private lemma stepD_real_mono : Monotone (fun t : ℝ => stepD t.toNNReal PUnit.unit) :=
  fun _ _ hab => stepD_mono PUnit.unit (Real.toNNReal_mono hab)

private lemma stepD_leftCont (ω : PUnit) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 => stepD s ω) (Iic t) t := by
  by_cases ht : t = 0
  · subst ht
    have hIic : Iic (0 : ℝ≥0) = {0} := Iic_bot
    rw [hIic]
    exact continuousWithinAt_singleton
  · have hpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht
    have hEq : (fun s : ℝ≥0 => stepD s ω) =ᶠ[𝓝[≤] t] (fun _ : ℝ≥0 => (1 : ℝ)) := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hpos)] with s hs
      have hs0 : s ≠ 0 := ne_of_gt hs
      simp [stepD, hs0]
    have hval : stepD t ω = 1 := by simp [stepD, ht]
    exact continuousWithinAt_const.congr_of_eventuallyEq hEq hval

private lemma stepD_rightLimit (t : ℝ≥0) (ω : PUnit) :
    rightLimit stepD t ω = 1 := by
  unfold rightLimit
  have hEq : (fun s : Ioi t => stepD s.1 ω) = fun _ => (1 : ℝ) := by
    ext ⟨s, hs⟩
    have hs0 : s ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hs)
    simp [stepD, hs0]
  have : Nonempty (Ioi t) := ⟨⟨t + 1, lt_add_one t⟩⟩
  rw [hEq, ciInf_const]

private lemma stepD_admissibleLe :
    IsAdmissibleLe zeroLevy 1 1 stepD := by
  refine ⟨⟨⟨fun _ => by simp [stepD], stepD_mono, stepD_leftCont, fun _ => measurable_const⟩, ?_⟩, ?_⟩
  · intro ω t _
    rw [stepD_rightLimit]
    unfold riskProcess zeroLevy stepD
    split_ifs <;> linarith
  · intro ω t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    unfold riskProcess zeroLevy stepD
    rw [if_neg ht0]
    norm_num

private lemma stepD_stieltjes_zero :
    stepD_real_mono.stieltjesFunction 0 = 1 := by
  rw [Monotone.stieltjesFunction_eq]
  have hEq : (fun t : ℝ => stepD t.toNNReal PUnit.unit) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have ht0 : t.toNNReal ≠ 0 := by
      simp [Real.toNNReal_eq_zero, not_le.mpr ht]
    simp [stepD, ht0]
  exact rightLim_eq_of_tendsto (tendsto_const_nhds.congr' hEq.symm)

private lemma stepD_stieltjes_neg {x : ℝ} (hx : x < 0) :
    stepD_real_mono.stieltjesFunction x = 0 := by
  rw [Monotone.stieltjesFunction_eq]
  have hEq : (fun t : ℝ => stepD t.toNNReal PUnit.unit) =ᶠ[𝓝[>] x] (fun _ => (0 : ℝ)) := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx)] with t (ht : t < 0)
    have ht0 : t.toNNReal = 0 := Real.toNNReal_of_nonpos ht.le
    simp [stepD, ht0]
  exact rightLim_eq_of_tendsto (tendsto_const_nhds.congr' hEq.symm)

private lemma stepD_stieltjes_leftLim_zero :
    Function.leftLim stepD_real_mono.stieltjesFunction 0 = 0 := by
  have hEq : (stepD_real_mono.stieltjesFunction : ℝ → ℝ) =ᶠ[𝓝[<] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
    exact stepD_stieltjes_neg hx
  exact leftLim_eq_of_tendsto (tendsto_const_nhds.congr' hEq.symm)

private lemma stepD_dividendMeasure_singleton_zero :
    dividendMeasure stepD PUnit.unit {0} = 1 := by
  unfold dividendMeasure
  rw [dif_pos stepD_real_mono]
  rw [StieltjesFunction.measure_singleton, stepD_stieltjes_zero, stepD_stieltjes_leftLim_zero]
  norm_num

theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
      {𝓕 : Filtration ℝ≥0 mΩ}
      (X : SpectrallyNegativeLevy P 𝓕)
      (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
      (hw_cont : ContinuousOn w (Ici 0))
      (hw_smooth :
        (¬ X.BoundedVariation →
          ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
        (X.BoundedVariation →
          ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
      (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
      (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
      (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
      (hxC : ENNReal.ofReal x ≤ C)
      (ω : Ω) (S : Set ℝ) (hCountable : S.Countable)
      (hNonneg : ∀ s ∈ S, 0 ≤ s)
      (hActive : ∀ s ∈ S,
        s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω),
      (∫⁻ s in S, ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (w x)) := by
  intro hAll
  let w : ℝ → ℝ := fun y => y - 1
  have hw_cont : ContinuousOn w (Ici 0) :=
    (continuous_id.sub continuous_const).continuousOn
  have hw_smooth :
      (¬ zeroLevy.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < 1}) ∧
      (zeroLevy.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < 1}) :=
    ⟨fun _ => (contDiff_id.sub contDiff_const).contDiffOn,
     fun _ => (contDiff_id.sub contDiff_const).contDiffOn⟩
  have hw_deriv : ∀ y : ℝ, deriv w y = 1 := by
    intro y
    change deriv (fun z : ℝ => z - 1) y = 1
    simp
  have hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < 1 →
      zeroLevy.GeneratorIntegrable w y ∧ zeroLevy.generator w y - 0 * w y ≤ 0 := by
    intro y _ _
    refine ⟨?_, ?_⟩
    · unfold SpectrallyNegativeLevy.GeneratorIntegrable zeroLevy
      simp [IntegrableOn]
    · unfold SpectrallyNegativeLevy.generator zeroLevy
      simp
  have hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < 1 → 1 ≤ deriv w y := by
    intro y _ _
    rw [hw_deriv y]
  have hxC : ENNReal.ofReal (1 : ℝ) ≤ (1 : ℝ≥0∞) := by simp
  have hCount : ({0} : Set ℝ).Countable := countable_singleton 0
  have hNonneg : ∀ s ∈ ({0} : Set ℝ), 0 ≤ s := by
    intro s hs
    rw [mem_singleton_iff.mp hs]
  have hActive : ∀ s ∈ ({0} : Set ℝ),
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime zeroLevy 1 stepD PUnit.unit := by
    intro s hs
    left
    rw [mem_singleton_iff.mp hs]
    simp
  have hBound := hAll zeroLevy 1 0 w 1 hw_cont hw_smooth hw_gen hw_grad stepD stepD_admissibleLe
    hxC PUnit.unit {0} hCount hNonneg hActive
  have hLHS :
      (∫⁻ s in ({0} : Set ℝ), ENNReal.ofReal (Real.exp (-((0 : ℝ) * s)))
        ∂(dividendMeasure stepD PUnit.unit)) = 1 := by
    simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one, setLIntegral_const,
      one_mul, stepD_dividendMeasure_singleton_zero]
  have hRHS : ENNReal.ofReal (w 1) = 0 := by
    change ENNReal.ofReal ((1 : ℝ) - 1) = 0
    simp
  rw [hLHS, hRHS] at hBound
  exact not_le_of_gt zero_lt_one hBound
