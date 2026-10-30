-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_ubv_clipped_ceiling_grid_killed_ost_eq_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:34:04.562922+00:00
-- url     : https://prove2.me/submissions/d121124f-602e-4c21-be8f-7fc9e8da56db

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_grid_ost_from_source
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- The true original-Lévy UBV continuously killed ceiling-grid scale reward
has expectation W(x) at every finite cap, with the actual clipped clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hx : 0 ≤ x)
    (a : ℝ) (T δ : ℝ≥0) (hδ : 0 < δ)
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
  have hStop := avram_root29_01_unbounded_killed_grid_ost_from_source
    X hnbv q x hq W hW hx clock hc hc0
      (-x) (a-x) (Nat.ceil (T / δ))
  simpa only [clock, ← hKc, NNReal.coe_min, NNReal.coe_mul] using hStop
