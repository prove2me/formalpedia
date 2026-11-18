-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_clipped_ceiling_grid_killed_ost_eq_nat_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:08:13.850204+00:00
-- url     : https://prove2.me/submissions/7940170f-ff09-4ff4-82fa-cfbacdd44c35

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_grid_optional_stopping
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hx : 0 ≤ x) (a : ℝ) (T δ : ℝ≥0) (hδ : 0 < δ)
    (K : Ω → ℕ)
    (hK : ∀ η, K η = hittingBtwn
      (fun (k : ℕ) ξ => max (X.X ((k : ℝ≥0) * δ) ξ - (a-x))
        ((-x) - X.X ((k : ℝ≥0) * δ) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / δ)) η) :
    (∫ ω,
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K η : ℝ≥0) * δ) T → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * ((min ((K η : ℝ≥0) * δ) T) : ℝ))) *
          W (x + X.X (min ((K η : ℝ≥0) * δ) T) η)) ω ∂P) = W x := by
  classical
  let clock : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * δ) T
  obtain ⟨hmono, hzero, _⟩ := chat03_clipped_grid_clock_bounded T δ
  have hK' (η : Ω) :
      K η = hittingBtwn
        (fun (j : ℕ) ξ => max (X.X (clock j) ξ - (a - x))
          ((-x) - X.X (clock j) ξ))
        (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / δ)) η := by
    rw [hK η]
    simpa only [clock] using
      (chat03_actual_ceiling_capped_grid_clipped_hitting_congr
        X (-x) (a - x) T δ hδ η)
  have hc0 : clock 0 = 0 := by simpa [clock] using hzero
  have hOST := avram_ws01b_bv_killed_scale_grid_optional_stopping
    X hX q x hq W hW hBV hx clock hmono hc0
      (-x) (a - x) (Nat.ceil (T / δ))
  simpa [hK', clock] using hOST
