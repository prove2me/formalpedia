-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_unit_atom_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:29:42.483125+00:00
-- url     : https://prove2.me/submissions/f2e1c0bf-3a14-4333-95e8-1d782d2d5269

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_unit_atom_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- The unit-magnitude truncation correction is Bochner integrable
under the Lévy truncated-square assumption, including an atom at one. -/
theorem solution (μ : Measure ℝ) (θ : ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    Integrable (({1} : Set ℝ).indicator (fun _ : ℝ => θ)) μ := by
  have hmass : μ ({1} : Set ℝ) < ⊤ :=
    gaussian_levy_unit_atom_finite μ hlevy
  have hconst : IntegrableOn (fun _ : ℝ => θ)
      ({1} : Set ℝ) μ :=
    integrableOn_const (ne_of_lt hmass)
  exact (integrable_indicator_iff
    (measurableSet_singleton (1 : ℝ))).mpr hconst
