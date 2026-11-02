-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_real_stopped_partition_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:59:32.331407+00:00
-- url     : https://prove2.me/submissions/5e4a99ac-c281-4445-bcca-dafe036dcb7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Almost surely the genuine original BV negative-mark source
measure is a finite nonnegative real interval functional whose
mass telescopes exactly along every ordered finite time partition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ J : ℝ≥0 → ℝ≥0 → ℝ,
      (∀ (a b : ℝ≥0),
        J a b =
          (∫⁻ p,
            (if a < p.1 ∧ p.1 ≤ b then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal) ∧
      (∀ a b, 0 ≤ J a b) ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (∑ i ∈ Finset.range n, J (u i) (u (i + 1))) =
          J (u 0) (u n) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity
      X hBV] with ω hω
  obtain ⟨J, hJdef, hJpos, hJadd⟩ := hω
  have hzero (s : ℝ≥0) : J s s = 0 := by
    have h := hJadd s s s le_rfl le_rfl
    linarith
  refine ⟨J, hJdef, hJpos, ?_⟩
  intro u hu n
  induction n with
  | zero =>
      simp [hzero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      exact (hJadd (u 0) (u n) (u (n + 1))
        (hu (Nat.zero_le n)) (hu (Nat.le_succ n))).symm
