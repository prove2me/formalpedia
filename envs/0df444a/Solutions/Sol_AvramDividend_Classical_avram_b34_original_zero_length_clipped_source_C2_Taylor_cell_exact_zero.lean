-- Prove2me | solution 1 for AvramDividend.Classical.avram_b34_original_zero_length_clipped_source_C2_Taylor_cell_exact_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:39:43.394039+00:00
-- url     : https://prove2.me/submissions/eeded5a3-f10d-4b2a-887e-4cd1bb9a6b52

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Zero-duration original physical clipped cells contribute no C2 Taylor remainder. -/
theorem solution
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration ℝ≥0 mOmega}
    (X : SpectrallyNegativeLevy P F)
    (x : ℝ) (D : ℝ≥0 → Omega → ℝ)
    (w : ℝ → ℝ) (S : Finset ℕ)
    (s t : ℕ → Omega → ℝ≥0) :
    ∀ omega : Omega,
      (∀ i ∈ S, s i omega = t i omega) →
      (∑ i ∈ S,
        let z : ℝ :=
          Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u omega - rightLimit D u omega) (s i omega)
        let g : ℝ :=
          X.X (t i omega) omega - X.X (s i omega) omega -
            (((t i omega : ℝ) - (s i omega : ℝ)) * X.c)
        (w (z + g) -
          taylorWithinEval w 1 (Set.uIcc z (z + g)) z (z + g) -
          (iteratedDeriv 2 w z * g ^ 2) / 2)) = 0 := by
  classical
  intro omega hclock
  apply Finset.sum_eq_zero
  intro i hi
  have ht : t i omega = s i omega := (hclock i hi).symm
  simp [ht, taylorWithinEval_self]
