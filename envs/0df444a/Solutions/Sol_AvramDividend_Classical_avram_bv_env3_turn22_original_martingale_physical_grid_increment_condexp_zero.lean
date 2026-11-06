-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:55:50.74629+00:00
-- url     : https://prove2.me/submissions/1a75132b-9f42-432f-9b66-91f53684dc76

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine original-filtration source martingale has centred chronological physical-grid increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (i : ℕ) :
    P[(fun ω => Y (u (i + 1)) ω - Y (u i) ω) | 𝓕.rightCont (u i)]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hinc := hMart.condExp_ae_eq (hu (Nat.le_succ i))
  have hstay := hMart.condExp_ae_eq (le_rfl : u i ≤ u i)
  calc
    P[(fun ω => Y (u (i + 1)) ω - Y (u i) ω) | 𝓕.rightCont (u i)]
        =ᵐ[P] (fun ω =>
          P[Y (u (i + 1)) | 𝓕.rightCont (u i)] ω -
            P[Y (u i) | 𝓕.rightCont (u i)] ω) := by
          exact condExp_sub (hMart.integrable (u (i + 1)))
            (hMart.integrable (u i)) (𝓕.rightCont (u i))
    _ =ᵐ[P] (fun ω => Y (u i) ω - Y (u i) ω) :=
      hinc.sub hstay
    _ =ᵐ[P] (fun _ => (0 : ℝ)) := by
      simp
