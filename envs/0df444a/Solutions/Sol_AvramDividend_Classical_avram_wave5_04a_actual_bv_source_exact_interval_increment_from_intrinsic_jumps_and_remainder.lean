-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:38:00.139535+00:00
-- url     : https://prove2.me/submissions/d7368d82-534a-41ef-8b9d-2cfd1890c8c9

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_source_negative_jump_series_interval_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact original BV source increment decomposition into drift, all
intrinsic source left jumps and one monotone downward finite-variation
remainder. This theorem does not claim that the remainder vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (s t : ℝ≥0) (hst : s ≤ t),
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∑' (u : ℝ≥0),
              if s < u ∧ u ≤ t then
                ENNReal.ofReal (Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
              else 0).toReal -
            (R t - R s) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_canonical_remainder_monotone X hBV,
      avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual X hBV]
    with ω hRmono hjumps
  classical
  let S (t : ℝ≥0) : ℝ := (t : ℝ) * X.drift - X.X t ω
  let jump (v : ℝ≥0) : ℝ≥0∞ :=
    ENNReal.ofReal (Function.leftLim
      (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
  let mass (a b : ℝ≥0) : ℝ≥0∞ :=
    ∑' (v : ℝ≥0), if a < v ∧ v ≤ b then jump v else 0
  let R (t : ℝ≥0) : ℝ := S t - (mass 0 t).toReal
  have hmass_le (a b : ℝ≥0) (hab : a ≤ b) :
      mass a b ≤ ENNReal.ofReal (S b - S a) := by
    simpa only [mass, jump, S] using hjumps a b hab
  have hmass_finite (a b : ℝ≥0) (hab : a ≤ b) :
      mass a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmass_le a b hab)
  refine ⟨R, ?_, hRmono, ?_⟩
  · intro t
    rfl
  intro s t hst
  have hsplit : mass 0 t = mass 0 s + mass s t := by
    simpa only [mass, jump] using
      (avram_wave5_04a_actual_source_negative_jump_series_interval_add
        X ω s t hst)
  have hsplit_real :
      (mass 0 t).toReal =
        (mass 0 s).toReal + (mass s t).toReal := by
    rw [hsplit]
    exact ENNReal.toReal_add
      (hmass_finite 0 s (show (0 : ℝ≥0) ≤ s from zero_le))
      (hmass_finite s t hst)
  have hinc : R t - R s =
      (S t - S s) - (mass s t).toReal := by
    change (S t - (mass 0 t).toReal) -
        (S s - (mass 0 s).toReal) =
      (S t - S s) - (mass s t).toReal
    rw [hsplit_real]
    ring
  change X.X t ω - X.X s ω =
    ((t : ℝ) - (s : ℝ)) * X.drift -
      (mass s t).toReal - (R t - R s)
  have hlinear : ((t : ℝ) - (s : ℝ)) * X.drift =
      (t : ℝ) * X.drift - (s : ℝ) * X.drift := by ring
  rw [hlinear]
  dsimp only [S] at hinc
  linarith only [hinc]
