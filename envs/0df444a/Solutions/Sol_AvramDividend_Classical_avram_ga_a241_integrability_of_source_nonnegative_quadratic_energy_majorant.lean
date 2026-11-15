-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a241_integrability_of_source_nonnegative_quadratic_energy_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:22:35.531654+00:00
-- url     : https://prove2.me/submissions/998a2103-19f5-4896-adea-97808c798cd9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F E : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m)
    (hFm : ∀ m, AEStronglyMeasurable (F m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hFpos : ∀ m ω, 0 ≤ F m ω)
    (hEpos : ∀ m ω, 0 ≤ E m ω)
    (hPt : ∀ m ω, F m ω ≤ 2 * E m ω + 2 * a m) :
    ∀ m, Integrable (F m) P := by
  intro m
  have hGI : Integrable
      (fun ω => 2 * E m ω + 2 * a m) P :=
    ((hEI m).const_mul 2).add (integrable_const (2 * a m))
  have hGpos (ω : Ω) :
      0 ≤ 2*E m ω+2*a m := by
    have h0 := hEpos m ω
    have h1 := ha m
    positivity
  apply Integrable.mono' hGI (hFm m)
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (hFpos m ω),
    abs_of_nonneg (hGpos ω)] using hPt m ω
