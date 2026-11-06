-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_finite_true_jump_strict_band_eventually
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:41:07.502253+00:00
-- url     : https://prove2.me/submissions/0324fd3a-70d0-42c8-bcb6-00219a910f51

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Finite actual original jump sets admit one common sufficiently fine physical band mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : Finset ℝ≥0) (lo hi : ℝ)
    (z : ℕ → ℝ≥0 → ℝ) (u : ℝ≥0 → ℝ)
    (hlim : ∀ t ∈ T, Tendsto (fun k => z k t) atTop (nhds (u t)))
    (hstrict : ∀ t ∈ T,
      u t ∈ Set.Ioo lo hi ∧
      u t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t) ∈ Set.Ioo lo hi) :
    ∀ᶠ k in atTop, ∀ t ∈ T,
      z k t ∈ Set.Icc lo hi ∧
      z k t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t) ∈ Set.Icc lo hi := by
  classical
  have hsingle : ∀ t ∈ T, ∀ᶠ k in atTop,
      z k t ∈ Set.Icc lo hi ∧
      z k t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t) ∈ Set.Icc lo hi := by
    intro t ht
    have hza := hlim t ht
    have hzb : Tendsto
        (fun k => z k t +
          (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t))
        atTop (nhds (u t +
          (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t))) :=
      hza.add tendsto_const_nhds
    have hU : Set.Ioo lo hi ∈ nhds (u t) :=
      isOpen_Ioo.mem_nhds (hstrict t ht).1
    have hV : Set.Ioo lo hi ∈ nhds (u t +
        (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) :=
      isOpen_Ioo.mem_nhds (hstrict t ht).2
    filter_upwards [hza.eventually hU, hzb.eventually hV] with k hk1 hk2
    exact ⟨⟨le_of_lt hk1.1, le_of_lt hk1.2⟩,
      ⟨le_of_lt hk2.1, le_of_lt hk2.2⟩⟩
  have hfinite : ∀ s : Finset ℝ≥0,
      (∀ t ∈ s, ∀ᶠ k in atTop,
        z k t ∈ Set.Icc lo hi ∧
        z k t + (X.X t ω - Function.leftLim
          (fun r : ℝ≥0 => X.X r ω) t) ∈ Set.Icc lo hi) →
      ∀ᶠ k in atTop, ∀ t ∈ s,
        z k t ∈ Set.Icc lo hi ∧
        z k t + (X.X t ω - Function.leftLim
          (fun r : ℝ≥0 => X.X r ω) t) ∈ Set.Icc lo hi := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      filter_upwards [] with k
      intro t ht
      simp at ht
    | @insert a s ha ih =>
      intro hs
      have haE := hs a (by simp)
      have hsE := ih (by
        intro t ht
        exact hs t (Finset.mem_insert_of_mem ht))
      filter_upwards [haE, hsE] with k hka hks
      intro t ht
      rcases Finset.mem_insert.mp ht with hta | hts
      · subst t
        exact hka
      · exact hks t hts
  exact hfinite T hsingle
