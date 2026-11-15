-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a238_integrable_raw_energy_uniform_expected_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:25:58.784997+00:00
-- url     : https://prove2.me/submissions/48499e80-5ca1-4b9c-9326-d2423d891b5f

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
    (F E : ℕ → Ω → ℝ) (a : ℕ → ℝ) (K B : ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hEBound : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (haBound : ∀ m, a m ≤ B)
    (hPt : ∀ m ω, F m ω ≤ 2 * E m ω + 2 * a m) :
    ∀ m, (∫ ω, F m ω ∂P) ≤ 2 * K + 2 * B := by
  intro m
  have hGI : Integrable (fun ω => 2 * E m ω + 2 * a m) P :=
    ((hEI m).const_mul 2).add (integrable_const (2 * a m))
  have hBound := integral_mono (hFI m) hGI (hPt m)
  have hEq : (∫ ω, 2 * E m ω + 2 * a m ∂P) =
      2 * (∫ ω, E m ω ∂P) + 2 * a m := by
    rw [integral_add ((hEI m).const_mul 2)
      (integrable_const (2 * a m))]
    simpa only [integral_const_mul, integral_const,
      probReal_univ, smul_eq_mul, one_mul]
  rw [hEq] at hBound
  linarith [hEBound m, haBound m]
