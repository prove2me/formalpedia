-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_original_BV_intrinsic_pure_jump_all_time_from_integer_horizon_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:19:43.78782+00:00
-- url     : https://prove2.me/submissions/5f7d4e9e-1dde-4404-a0d8-c87f0422b5cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Source-faithful reduction of the full BV Lévy pure-jump equality to
countably many integer-horizon identities for the same original process.
The additional integer identities remain a genuine compensator obligation;
this theorem does not assume the desired equality at noninteger times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hIntegers : ∀ n : ℕ, ∀ᵐ ω ∂P,
      X.X (n : ℝ≥0) ω =
        ((n : ℝ≥0) : ℝ) * X.drift -
          (∫⁻ p,
            (if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) then
              ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∫⁻ p,
          (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
  filter_upwards
    [(avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
      X hStanding hBV).2, (ae_all_iff.mpr hIntegers)] with ω hsource hnat
  obtain ⟨R, _hRdef, _hRzero, hRmono, hpath⟩ := hsource
  have hRnat (n : ℕ) : R (n : ℝ≥0) = 0 := by
    have hsourceNat := (hpath (n : ℝ≥0)).2
    have hgiven := hnat n
    linarith only [hsourceNat, hgiven]
  intro t
  obtain ⟨n, htnReal⟩ := exists_nat_ge (t : ℝ)
  have htn : t ≤ (n : ℝ≥0) := by exact_mod_cast htnReal
  have hRvanishes : R t = 0 := by
    have hnonneg := (hpath t).1
    have hupper : R t ≤ R (n : ℝ≥0) := hRmono htn
    rw [hRnat n] at hupper
    exact le_antisymm hupper hnonneg
  have hsourceT := (hpath t).2
  simpa [hRvanishes] using hsourceT
