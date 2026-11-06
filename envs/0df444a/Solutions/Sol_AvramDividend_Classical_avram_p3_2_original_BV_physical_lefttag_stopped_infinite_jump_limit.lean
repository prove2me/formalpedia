-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_BV_physical_lefttag_stopped_infinite_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:39:40.407771+00:00
-- url     : https://prove2.me/submissions/17d204db-0d9d-4c51-9228-521b3ea408d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_BV_stopped_dominated_nonlinear_jump_source_limit
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_C1_compact_stopped_jump_increment_dominator
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (S : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (w : ℝ → ℝ) (U : Set ℝ)
      (hw : ContDiffOn ℝ 1 w U) (hU : IsOpen U)
      (lo hi : ℝ) (hSub : Set.Icc lo hi ⊆ U)
      (lefttag : ℕ → ℝ≥0 → ℝ≥0)
      (discount : ℝ≥0 → ℝ) (M : ℝ),
      0 ≤ M →
      (∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 →
        Tendsto (fun k => lefttag k t) atTop (𝓝[<] t)) →
      (∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 →
        (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) ∈ U ∧
        (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ∈ U) →
      (∀ᶠ k in atTop, ∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 →
        (x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω) ∈ Set.Icc lo hi ∧
        ((x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω)) + (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ∈ Set.Icc lo hi) →
      (∀ t : ℝ≥0, |discount t| ≤ M) →
      Tendsto
        (fun k => ∑' t : ℝ≥0,
          if 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 then
            discount t *
              (w ((x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω) + (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t)) - w (x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω))
          else 0) atTop
        (nhds (∑' t : ℝ≥0,
          if 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t) ≠ 0 then
            discount t *
              (w ((Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) t)) - w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t))
          else 0)) := by
  filter_upwards
    [avram_p3_2_original_BV_stopped_dominated_nonlinear_jump_source_limit
      X hBV S] with ω hω
  intro w U hw hU lo hi hSub lefttag discount M hM
    hTag hInside hBand hDisc
  let z : ℕ → ℝ≥0 → ℝ := fun k t =>
    x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω
  let p : ℝ≥0 → ℝ := fun t =>
    Function.leftLim
      (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t
  obtain ⟨L, hL, hLip⟩ :=
    avram_p3_2_original_C1_compact_stopped_jump_increment_dominator
      X ω w U hw lo hi hSub S z hBand
  have hz (t : ℝ≥0) (ht : 0 < t ∧ t ≤ S ∧
      X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t ≠ 0) :
      Tendsto (fun k => z k t) atTop (nhds (p t)) :=
    (avram_p3_2_original_controlled_left_prestate_tendsto
      X x D hD ω t ht.1).comp (hTag t ht)
  have hc (t : ℝ≥0) (ht : 0 < t ∧ t ≤ S ∧
      X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t ≠ 0) :
      ContinuousAt w (p t) ∧
      ContinuousAt w (p t + (X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)) := by
    have hin := hInside t ht
    exact ⟨hw.continuousOn.continuousAt (hU.mem_nhds hin.1),
      hw.continuousOn.continuousAt (hU.mem_nhds hin.2)⟩
  exact hω w z p discount L M hL hM hz hc hLip hDisc
