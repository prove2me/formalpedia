-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_physical_lefttag_C1_nonlinear_jump_source_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:20:37.783856+00:00
-- url     : https://prove2.me/submissions/efaf8965-fba6-43bd-a903-b05e8fab50ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_tag_prejump_nonlinear_source_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-! Left-tag original X/D nonlinear jump convergence on every finite physical time set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (hU : IsOpen U)
    (T : Finset ℝ≥0) (hT : ∀ t ∈ T, 0 < t)
    (lefttag : ℕ → ℝ≥0 → ℝ≥0)
    (hTag : ∀ t ∈ T,
      Tendsto (fun k => lefttag k t) atTop (𝓝[<] t))
    (discount : ℝ≥0 → ℝ)
    (hInside : ∀ t ∈ T,
      Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t ∈ U ∧
      (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t) ∈ U) :
    Tendsto
      (fun k => T.sum (fun t =>
        discount t *
          (w ((x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω) + (X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t)) -
           w (x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω)))) atTop
      (nhds (T.sum (fun t =>
        discount t *
          (w ((Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) + (X.X t ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) t)) -
           w (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t))))) := by
  let u : ℝ≥0 → ℝ := fun t =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v ω - rightLimit D v ω) t
  let z : ℕ → ℝ≥0 → ℝ := fun k t =>
    x + X.X (lefttag k t) ω - rightLimit D (lefttag k t) ω
  have hz : ∀ t ∈ T, Tendsto (fun k => z k t) atTop (nhds (u t)) := by
    intro t ht
    exact (avram_p3_2_original_controlled_left_prestate_tendsto
      X x D hD ω t (hT t ht)).comp (hTag t ht)
  have hcont : ContinuousOn w U := hw.continuousOn
  have hwt : ∀ t ∈ T,
      ContinuousAt w (u t) ∧
      ContinuousAt w (u t +
        (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hInside t ht
    exact ⟨hcont.continuousAt (hU.mem_nhds h1),
      hcont.continuousAt (hU.mem_nhds h2)⟩
  exact avram_p3_2_original_finite_tag_prejump_nonlinear_source_limit
    X ω w T z u discount hz hwt
