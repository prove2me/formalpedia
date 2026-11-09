-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail13_original_single_reset_infinite_cap_admissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:50:50.45186+00:00
-- url     : https://prove2.me/submissions/57d0f922-8ac9-41b5-a0e9-a9c186288801

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_single_positive_clock_reset_admissible
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_rightLimit_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_original_single_reset_isDividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original reserve clipped at zero pays an affordable dividend strictly
after one positive clock; this is genuinely admissible for infinite cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (s : ℝ≥0) (hs : 0 < s) :
    IsAdmissibleLe X x ⊤ (fun t ω =>
      if t ≤ s then 0 else max (x + X.X s ω) (0 : ℝ)) := by
  let K : Ω → ℝ := fun ω => max (x + X.X s ω) (0 : ℝ)
  let D : ℝ≥0 → Ω → ℝ := fun t ω => if t ≤ s then 0 else K ω
  have hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω := by
    intro t ω
    rfl
  have hK : ∀ ω, 0 ≤ K ω := by
    intro ω
    exact le_max_right _ _
  have hstrategy : IsDividendStrategy 𝓕 D :=
    avram_bv_tail13_original_single_reset_isDividendStrategy X x s
  have hright : ∀ ω t, rightLimit D t ω = if t < s then 0 else K ω :=
    avram_bv_tail13_single_step_rightLimit_eq D s K hK hD
  have hafford : ∀ ω, (s : ℝ≥0∞) < ruinTime X x D ω →
      K ω ≤ x + X.X s ω := by
    intro ω hpre
    have hreserve : 0 ≤ x + X.X s ω := by
      have hnonneg := riskProcess_nonneg_before_ruin X x D ω s hpre
      simpa [riskProcess, D] using hnonneg
    dsimp [K]
    rw [max_eq_left hreserve]
  exact avram_bv_tail12_single_positive_clock_reset_admissible
    X x hx s hs K D hD hstrategy hright hafford
