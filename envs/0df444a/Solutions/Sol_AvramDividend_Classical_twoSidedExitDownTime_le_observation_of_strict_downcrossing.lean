-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_le_observation_of_strict_downcrossing
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:10:27.583003+00:00
-- url     : https://prove2.me/submissions/b5043ca7-e33b-45cb-8cef-44d26dc7cdf4

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

noncomputable def S189zeroLevy :
    SpectrallyNegativeLevy (Measure.dirac ()) (⊥ : Filtration ℝ≥0 (⊤ : MeasurableSpace Unit)) where
  X := fun _ _ => 0
  c := 0
  σ := 0
  ν := 0
  isProbability := inferInstance
  σ_nonneg := le_rfl
  ν_Ici := rfl
  ν_integrable := by simp
  X_zero := fun _ => rfl
  rightCont := fun _ _ => continuousWithinAt_const
  leftLim := fun _ _ _ => ⟨0, tendsto_const_nhds⟩
  noPosJumps := fun ω t l ht hl => by
    have : (𝓝[<] t).NeBot := nhdsWithin_Iio_self_neBot' ⟨0, ht⟩
    exact (tendsto_nhds_unique hl tendsto_const_nhds).symm.le
  adapted := fun _ => measurable_const
  indepIncrements := fun s t _ => by
    rw [Indep_iff]
    intro A B _ _
    rcases Set.subsingleton_or_nontrivial A with hA | hA <;>
    rcases Set.subsingleton_or_nontrivial B with hB | hB
    all_goals first
      | (rcases hA.eq_empty_or_singleton with rfl | ⟨a, rfl⟩ <;>
         rcases hB.eq_empty_or_singleton with rfl | ⟨b, rfl⟩ <;> simp)
      | (exfalso; obtain ⟨x, -, y, -, hxy⟩ := hA; exact hxy rfl)
      | (exfalso; obtain ⟨x, -, y, -, hxy⟩ := hB; exact hxy rfl)
  stationaryIncrements := fun s t _ => by
    simp only [sub_self]; exact IdentDistrib.refl measurable_const.aemeasurable
  laplace := fun t θ _ => by
    simp [laplaceExponent]

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (s : ℝ≥0)
    (hs : X.X s ω < -x),
    twoSidedExitDownTime X x ω ≤ (s : ℝ≥0∞)) := by
  intro h
  have h1 := h S189zeroLevy (-1) () 0 (by simp [S189zeroLevy])
  have h2 : twoSidedExitDownTime S189zeroLevy (-1) () = ⊤ := by
    simp [twoSidedExitDownTime, S189zeroLevy]
  rw [h2] at h1
  simp at h1
