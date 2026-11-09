-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail13_original_reset_affine_jump_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:40:42.840303+00:00
-- url     : https://prove2.me/submissions/5a32c4bf-b62c-49d7-ab23-317f0d595217

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_rightLimit_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_single_positive_clock_reset_affine_jump_contact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual surplus reset at a positive clock satisfies the source-exact
affine dividend-jump verification inequality before ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (s : ℝ≥0) (hs : 0 < s)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else
      max (x + X.X s ω) (0 : ℝ)) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        (fun y : ℝ => if y < 0 then 0 else 1 + y) (riskProcess X x D t ω) -
          (fun y : ℝ => if y < 0 then 0 else 1 + y)
            (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by
  let K : Ω → ℝ := fun ω => max (x + X.X s ω) (0 : ℝ)
  have hD' : ∀ t ω, D t ω = if t ≤ s then 0 else K ω := hD
  have hK : ∀ ω, 0 ≤ K ω := by
    intro ω
    exact le_max_right _ _
  have hright : ∀ ω t, rightLimit D t ω = if t < s then 0 else K ω :=
    avram_bv_tail13_single_step_rightLimit_eq D s K hK hD'
  have hreset : ∀ ω, (s : ℝ≥0∞) < ruinTime X x D ω →
      K ω = x + X.X s ω := by
    intro ω hpre
    have hreserve : 0 ≤ x + X.X s ω := by
      have hnonneg := riskProcess_nonneg_before_ruin X x D ω s hpre
      have hDs : D s ω = 0 := by
        rw [hD]
        simp
      simpa [riskProcess, hDs] using hnonneg
    exact max_eq_left hreserve
  exact avram_bv_tail12_single_positive_clock_reset_affine_jump_contact
    X x s hs K D hD' hright hK hreset
