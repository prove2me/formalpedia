-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess29_original_finite_BV_collision_and_width_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:01:31.860778+00:00
-- url     : https://prove2.me/submissions/1924eba7-e551-4c40-8ca9-354abeea18c7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess27_original_measurable_drift_count_collision_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess28_original_fullmark_uniform_width_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess26_original_grid_drift_deficit_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Both original physical contact errors vanish in mean on one genuine grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0) (cells : ℕ → ℕ)
    (hStrict : ∀ n, StrictMono (grid n))
    (hZero : ∀ n, grid n 0 = 0)
    (hEnd : ∀ n, grid n (cells n) = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in (Filter.atTop : Filter ℕ),
        ∀ i : ℕ, i < cells n →
          dist (grid n i) (grid n (i + 1)) < δ) :
    Filter.Tendsto (fun n : ℕ => ∫⁻ ω,
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) - (∑ i ∈ Finset.range (cells n),
        if X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
           X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))
        then (1 : ℝ≥0∞) else 0)) +
        (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  classical
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
  let K : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∑ i ∈ Finset.range (cells n),
      if X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
          X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))
      then (1 : ℝ≥0∞) else 0
  let A : ℕ → Ω → ℝ≥0∞ := fun n ω => N ω - K n ω
  let W : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω
  have hA : Filter.Tendsto (fun n => ∫⁻ ω, A n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    exact avram_bv_excess27_original_measurable_drift_count_collision_L1_vanish
      X hBV hFinite T hT grid cells hStrict hZero hEnd hMesh
  have hW : Filter.Tendsto (fun n => ∫⁻ ω, W n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    exact avram_bv_excess28_original_fullmark_uniform_width_L1_vanish
      X hBV hFinite T hT
  have hmN : Measurable N := by
    exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le) Set.univ MeasurableSet.univ
  have hmA (n : ℕ) : Measurable (A n) := by
    exact hmN.sub
      (avram_bv_excess26_original_grid_drift_deficit_count_measurable
        X (grid n) (cells n))
  have hadd (n : ℕ) :
      (∫⁻ ω, A n ω + W n ω ∂P) =
      (∫⁻ ω, A n ω ∂P) + (∫⁻ ω, W n ω ∂P) := by
    exact lintegral_add_left (hmA n) (W n)
  change Filter.Tendsto (fun n => ∫⁻ ω, A n ω + W n ω ∂P)
    Filter.atTop (nhds (0 : ℝ≥0∞))
  have hsum := hA.add hW
  simpa only [zero_add] using
    (hsum.congr' (Filter.Eventually.of_forall fun n => (hadd n).symm))
