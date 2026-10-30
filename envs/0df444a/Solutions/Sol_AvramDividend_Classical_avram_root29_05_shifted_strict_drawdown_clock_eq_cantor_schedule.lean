-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:28:26.887997+00:00
-- url     : https://prove2.me/submissions/6cb10bea-e09e-475d-b1b8-5e921ec0330f

import Mathlib.Topology.Order
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous
import Theorems.Thm_AvramDividend_Classical_shiftedSup_right_continuous_of_levy
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightNhds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- Every shifted genuine Lévy future has its strict drawdown first-passage
clock on the same dense Cantor schedule used for sampled regulator payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) (a : ℝ) :
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
     ⨅ i : {t : ℝ≥0 // f t - M t < -a}, (i.1 : ℝ≥0∞)) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
     let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ⨅ j : ℕ, if f (samples j) - M (samples j) < -a
       then (samples j : ℝ≥0∞) else ⊤) := by
  let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
  let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
  have hRight : ∀ s : ℝ≥0, f s - M s < -a →
      ∃ v : ℝ≥0, s < v ∧
        ∀ r : ℝ≥0, s ≤ r → r < v → f r - M r < -a := by
    intro s hs
    have hcont : ContinuousWithinAt (fun t : ℝ≥0 => f t - M t)
        (Ici s) s := by
      exact (shiftedLevy_increments_right_continuous X ω u s).sub
        ((shiftedSup_right_continuous_of_levy X ω u) s)
    have hev_ge : ∀ᶠ r in 𝓝[≥] s, f r - M r < -a :=
      hcont.tendsto.eventually (Iio_mem_nhds hs)
    have hev_gt : ∀ᶠ r in 𝓝[>] s, f r - M r < -a :=
      hev_ge.filter_mono (nhdsWithin_mono s Ioi_subset_Ici_self)
    rcases mem_nhdsGT_iff_exists_Ioo_subset.mp
      (show {r : ℝ≥0 | f r - M r < -a} ∈ 𝓝[>] s from hev_gt) with
      ⟨v, hsv, hv⟩
    refine ⟨v, hsv, ?_⟩
    intro r hsr hrv
    rcases eq_or_lt_of_le hsr with heq | hlt
    · simpa [heq] using hs
    · exact hv ⟨hlt, hrv⟩
  simpa only [f, M, ENNReal.coe_mul, ENNReal.coe_inv] using
    (rightInterval_lower_strictExit_eq_schedule
      (fun t : ℝ≥0 => f t - M t) (-a) hRight)
