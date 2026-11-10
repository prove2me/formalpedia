-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_step_local_reserve_positive_of_right_continuity
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T09:48:53.581584+00:00
-- url     : https://prove2.me/submissions/45689d08-8fc2-4451-81ee-efad50b02590

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

open ProbabilityTheory Filter Topology

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

theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
      {𝓕 : Filtration ℝ≥0 mΩ}
      (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ) (ω : Ω)
      (_hright : ∀ t : ℝ≥0,
        rightLimit (fun s η => if s = 0 then 0 else K η) t ω = K ω)
      (_hzero : X.X 0 ω = 0)
      (_hcont : ContinuousAt (fun t : ℝ≥0 => X.X t ω) 0)
      (_hgap : K ω < x),
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ →
        0 ≤ riskProcess X x (fun s η => if s = 0 then 0 else K η) t ω) := by
  intro hAll
  let K : PUnit → ℝ := fun _ => -2
  have hright : ∀ t : ℝ≥0,
      rightLimit (fun s η => if s = 0 then 0 else K η) t PUnit.unit = K PUnit.unit := by
    intro t
    unfold rightLimit
    have hEq : (fun s : Ioi t => if s.1 = 0 then (0 : ℝ) else K PUnit.unit) =
        fun _ => K PUnit.unit := by
      ext ⟨s, hs⟩
      have hs0 : s ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hs)
      simp [hs0]
    have : Nonempty (Ioi t) := ⟨⟨t + 1, lt_add_one t⟩⟩
    rw [hEq, ciInf_const]
  have hgap : K PUnit.unit < (-1 : ℝ) := by
    change (-2 : ℝ) < -1
    norm_num
  rcases hAll zeroLevy (-1) K PUnit.unit hright rfl continuousAt_const hgap with ⟨δ, hδ_pos, hδ⟩
  have h0 := hδ 0 hδ_pos
  unfold riskProcess zeroLevy at h0
  simp at h0
  linarith
