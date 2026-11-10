-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T09:50:43.074575+00:00
-- url     : https://prove2.me/submissions/ab5b251a-f035-43f0-822b-d916fac07288

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical MeasureTheory
open scoped NNReal

open ProbabilityTheory Filter Set Topology

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

private lemma stepD_isDividendStrategy :
    IsDividendStrategy zeroFiltration stepD :=
  ⟨fun _ => by simp [stepD], stepD_mono, stepD_leftCont, fun _ => measurable_const⟩

private lemma stepD_rightLimit_zero :
    rightLimit stepD 0 PUnit.unit = 1 := by
  unfold rightLimit
  have hEq : (fun s : Ioi (0 : ℝ≥0) => stepD s.1 PUnit.unit) = fun _ => (1 : ℝ) := by
    ext ⟨s, hs⟩
    have hs0 : s ≠ 0 := ne_of_gt hs
    simp [stepD, hs0]
  have : Nonempty (Ioi (0 : ℝ≥0)) := ⟨⟨1, mem_Ioi.mpr zero_lt_one⟩⟩
  rw [hEq, ciInf_const]

theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
      {𝓕 : Filtration ℝ≥0 mΩ}
      (X : SpectrallyNegativeLevy P 𝓕)
      (Y : SpectrallyNegativeLevy P 𝓕)
      (_hYν : Y.ν = 0) (_hYσ : Y.σ = X.σ)
      (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
      (_hSourceDecomp : ∀ (u : ℝ≥0) (η : Ω),
        X.X u η = (u : ℝ) * X.c +
          (Y.X u η - (u : ℝ) * Y.c) + Jsmall u η + Jlarge u η)
      (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
      (_hD : IsDividendStrategy 𝓕 D)
      (t : ℝ≥0) (ω : Ω),
      riskProcess X x D t ω =
        x + ((t : ℝ) * X.c +
          (Y.X t ω - (t : ℝ) * Y.c) +
            Jsmall t ω + Jlarge t ω) - rightLimit D t ω) := by
  intro hAll
  have hDecomp : ∀ (u : ℝ≥0) (η : PUnit),
      zeroLevy.X u η = (u : ℝ) * zeroLevy.c +
        (zeroLevy.X u η - (u : ℝ) * zeroLevy.c) + (fun _ _ => (0 : ℝ)) u η + (fun _ _ => (0 : ℝ)) u η := by
    intro u _
    change (0 : ℝ) = (u : ℝ) * 0 + (0 - (u : ℝ) * 0) + 0 + 0
    ring
  have hEq := hAll zeroLevy zeroLevy rfl rfl (fun _ _ => 0) (fun _ _ => 0)
    hDecomp 0 stepD stepD_isDividendStrategy 0 PUnit.unit
  rw [stepD_rightLimit_zero] at hEq
  unfold riskProcess zeroLevy stepD at hEq
  norm_num at hEq
