-- Prove2me | solution 1 for AvramDividend.Classical.two_sided_exit_min_is_stopping_time
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T08:24:40.3794+00:00
-- url     : https://prove2.me/submissions/9db826e0-a3ea-43b8-b199-fc51f4ce0d49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

open ProbabilityTheory Filter Set Topology

private noncomputable def counterFiltration :
    Filtration ℝ≥0 (⊤ : MeasurableSpace Bool) where
  seq t := if t = 0 then ⊥ else ⊤
  mono' i j hij := by
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]
    subst hj
    exact absurd (nonpos_iff_eq_zero.mp hij) hi
  le' i := by
    by_cases hi : i = 0 <;> simp [hi]

private def counterPath (t : ℝ≥0) (ω : Bool) : ℝ :=
  if ω then -(t : ℝ) else 0

private lemma counterPath_continuous (ω : Bool) :
    Continuous (fun s : ℝ≥0 => counterPath s ω) := by
  cases ω
  · exact continuous_const
  · change Continuous (fun s : ℝ≥0 => -(s : ℝ))
    exact continuous_neg.comp NNReal.continuous_coe

private lemma nhdsWithin_Iio_neBot_of_pos {t : ℝ≥0} (ht : 0 < t) :
    (𝓝[<] t).NeBot := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  have hne : (Iio t).Nonempty := ⟨0, ht⟩
  rw [closure_Iio' hne]
  exact le_refl t

private noncomputable def counterLevy :
    SpectrallyNegativeLevy (Measure.dirac false) counterFiltration where
  X := counterPath
  c := 0
  σ := 0
  ν := 0
  isProbability := inferInstance
  σ_nonneg := le_rfl
  ν_Ici := by simp
  ν_integrable := by simp
  X_zero ω := by simp [counterPath]
  rightCont ω t := (counterPath_continuous ω).continuousAt.continuousWithinAt
  leftLim ω t _ := ⟨counterPath t ω, (counterPath_continuous ω).continuousAt.continuousWithinAt⟩
  noPosJumps ω t l ht hl := by
    have : (𝓝[<] t).NeBot := nhdsWithin_Iio_neBot_of_pos ht
    have hlim : Tendsto (fun s => counterPath s ω) (𝓝[<] t) (𝓝 (counterPath t ω)) :=
      (counterPath_continuous ω).continuousAt.continuousWithinAt
    rw [tendsto_nhds_unique hl hlim]
  adapted t := by
    by_cases ht : t = 0
    · subst ht
      have h0 : counterPath 0 = fun _ : Bool => (0 : ℝ) := by
        ext ω
        simp [counterPath]
      rw [h0]
      exact measurable_const
    · intro s _
      change MeasurableSet[if t = 0 then ⊥ else ⊤] _
      rw [if_neg ht]
      trivial
  indepIncrements s t _ := by
    rw [ProbabilityTheory.Indep_iff]
    intro t₁ t₂ _ _
    have hm1 : MeasurableSet t₁ := trivial
    have hm2 : MeasurableSet t₂ := trivial
    simp [Measure.dirac_apply' _ hm1, Measure.dirac_apply' _ hm2,
      Measure.dirac_apply' _ (hm1.inter hm2), Set.indicator]
    by_cases h1 : false ∈ t₁ <;> by_cases h2 : false ∈ t₂ <;> simp [h1, h2]
  stationaryIncrements s t hst := by
    have heq : (fun ω => counterPath t ω - counterPath s ω) = counterPath (t - s) := by
      ext ω
      cases ω <;> simp [counterPath, NNReal.coe_sub hst]
      ring
    rw [heq]
    exact IdentDistrib.refl (measurable_of_finite _).aemeasurable
  laplace t θ _ := by
    refine ⟨Integrable.of_finite, ?_⟩
    rw [integral_dirac]
    simp [counterPath, laplaceExponent]

private lemma downTime_true_eq_zero :
    twoSidedExitDownTime counterLevy (-0) true = 0 := by
  rw [← nonpos_iff_eq_zero]
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  rw [zero_add]
  have hlt : counterLevy.X ε true < -0 := by
    change -(ε : ℝ) < -0
    exact neg_lt_neg (by exact_mod_cast hε)
  exact iInf₂_le ε hlt

private lemma upTime_false_eq_top :
    twoSidedExitUpTime counterLevy (1 - 0) false = ⊤ := by
  simp only [twoSidedExitUpTime, iInf_eq_top]
  intro t ht
  change (1 : ℝ) - 0 < 0 at ht
  linarith

private lemma downTime_false_eq_top :
    twoSidedExitDownTime counterLevy (-0) false = ⊤ := by
  simp only [twoSidedExitDownTime, iInf_eq_top]
  intro t ht
  change (0 : ℝ) < -0 at ht
  linarith

theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
      {𝓕 : Filtration ℝ≥0 mΩ}
      (X : SpectrallyNegativeLevy P 𝓕)
      (a x : ℝ),
      MeasureTheory.IsStoppingTime 𝓕
        (fun ω => min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))) := by
  intro hAll
  have hStop := hAll counterLevy 1 0
  have hMeas0 : MeasurableSet[counterFiltration 0]
      {ω : Bool | min (twoSidedExitUpTime counterLevy (1 - 0) ω)
        (twoSidedExitDownTime counterLevy (-0) ω) ≤ (0 : ℝ≥0)} := hStop 0
  change MeasurableSet[if (0 : ℝ≥0) = 0 then ⊥ else ⊤] _ at hMeas0
  rw [if_pos rfl, MeasurableSpace.measurableSet_bot_iff] at hMeas0
  have hTrue : true ∈
      {ω : Bool | min (twoSidedExitUpTime counterLevy (1 - 0) ω)
        (twoSidedExitDownTime counterLevy (-0) ω) ≤ (0 : ℝ≥0)} := by
    simp only [Set.mem_ofPred_eq, ENNReal.coe_zero]
    exact le_trans (min_le_right _ _) (by rw [downTime_true_eq_zero])
  have hFalse : false ∉
      {ω : Bool | min (twoSidedExitUpTime counterLevy (1 - 0) ω)
        (twoSidedExitDownTime counterLevy (-0) ω) ≤ (0 : ℝ≥0)} := by
    simp only [Set.mem_ofPred_eq, ENNReal.coe_zero, upTime_false_eq_top, downTime_false_eq_top,
      min_self, top_le_iff]
    exact ENNReal.zero_ne_top
  rcases hMeas0 with hEmpty | hUniv
  · rw [hEmpty] at hTrue
    exact hTrue
  · apply hFalse
    rw [hUniv]
    exact Set.mem_univ _
