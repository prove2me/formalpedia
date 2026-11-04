-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_cap_start_inner_band_grid_exit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:24:34.310954+00:00
-- url     : https://prove2.me/submissions/863d7306-833e-4484-ad38-4ea4f8808660

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An unpaid cap-start makes every strict-subcap sampled first-exit clock zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c x : ℝ) (hc : 0 < c) (hxc : x = c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (hNoInitialPayment : rightLimit D 0 ω = 0)
    (r : ℕ → ℝ≥0) (hr0 : r 0 = 0)
    (lower upper : ℝ) (hUpper : upper < c)
    (B : ℝ≥0) :
    min (⨅ k : ℕ,
      if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
         upper < x + X.X (r k) ω - rightLimit D (r k) ω
      then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0)
      = (0 : WithTop ℝ≥0) := by
  have hSample :
      x + X.X (r 0) ω - rightLimit D (r 0) ω = c := by
    rw [hr0, X.X_zero ω, hNoInitialPayment]
    simpa using hxc
  have hUpper0 :
      upper < x + X.X (r 0) ω - rightLimit D (r 0) ω := by
    simpa [hSample] using hUpper
  have hExit0 :
      x + X.X (r 0) ω - rightLimit D (r 0) ω < lower ∨
      upper < x + X.X (r 0) ω - rightLimit D (r 0) ω :=
    Or.inr hUpper0
  have hFirst : (⨅ k : ℕ,
      if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
         upper < x + X.X (r k) ω - rightLimit D (r k) ω
      then (r k : WithTop ℝ≥0) else ⊤) ≤ (0 : WithTop ℝ≥0) := by
    calc
      _ ≤ (if x + X.X (r 0) ω - rightLimit D (r 0) ω < lower ∨
          upper < x + X.X (r 0) ω - rightLimit D (r 0) ω
        then (r 0 : WithTop ℝ≥0) else ⊤) := iInf_le _ 0
      _ = (r 0 : WithTop ℝ≥0) := if_pos hExit0
      _ = (0 : WithTop ℝ≥0) := by simp [hr0]
  exact le_antisymm (le_trans (min_le_left _ _) hFirst) bot_le
