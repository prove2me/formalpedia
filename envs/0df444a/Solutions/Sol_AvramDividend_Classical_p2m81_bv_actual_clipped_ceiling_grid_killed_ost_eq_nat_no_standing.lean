-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_actual_clipped_ceiling_grid_killed_ost_eq_nat_no_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:52:36.916103+00:00
-- url     : https://prove2.me/submissions/38840110-40c5-47f1-9814-6f225684e0b1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_killed_scale_martingale_no_standing_public
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_grid_optional_stopping_of_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- The actual capped ceiling first-exit grid has exact standing-free BV killed q-scale expectation W(x). -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (a : ℝ) (T δ : ℝ≥0) (hδ : 0 < δ)
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
  have hKilled := p2m81_bv_killed_scale_martingale_no_standing_public
    X q φ hq hφ hroot W hW hBV x
  let clock : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * δ) T
  have hc : Monotone clock := (chat03_clipped_grid_clock_bounded T δ).1
  have hc0 : clock 0 = 0 := by simp [clock]
  have hKc : ∀ η, K η = hittingBtwn
      (fun (k : ℕ) ξ => max (X.X (clock k) ξ - (a-x))
        ((-x) - X.X (clock k) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / δ)) η := by
    intro η
    rw [hK η]
    exact chat03_actual_ceiling_capped_grid_clipped_hitting_congr
      X (-x) (a-x) T δ hδ η
  have hStop := chat03_killed_scale_grid_optional_stopping_of_martingale
    X q x W hx hKilled clock hc hc0 (-x) (a-x) (Nat.ceil (T / δ))
  simpa only [clock, ← hKc, NNReal.coe_min, NNReal.coe_mul] using hStop
