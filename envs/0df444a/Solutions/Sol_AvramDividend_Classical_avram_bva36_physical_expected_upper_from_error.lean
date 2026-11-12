-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva36_physical_expected_upper_from_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:20:50.568891+00:00
-- url     : https://prove2.me/submissions/431aff8b-282d-413b-a9ab-8acb9ab2f298

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-- An integrable source certificate gives an eventual expected budget. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F M E : ℕ → Ω → ℝ) (b : ℝ)
    (hF : ∀ n, Integrable (F n) P)
    (hM : ∀ n, Integrable (M n) P)
    (hE : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hMean : ∀ n, (∫ ω, M n ω ∂P) ≤ 0)
    (hBound : ∀ n, ∀ᵐ ω ∂P, F n ω ≤ b + M n ω + max (E n ω) 0)
    (hVan : Tendsto (fun n => ∫ ω, max (E n ω) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (∫ ω, F n ω ∂P) ≤ b + ε := by
  intro ε hε
  have hSmall : ∀ᶠ n in atTop,
      (∫ ω, max (E n ω) 0 ∂P) < ε :=
    hVan.eventually (Iio_mem_nhds hε)
  filter_upwards [hSmall] with n hn
  have hUpper : Integrable (fun ω => b + M n ω + max (E n ω) 0) P :=
    ((integrable_const _).add (hM n)).add (hE n)
  have hCmp := integral_mono_ae (hF n) hUpper (hBound n)
  have hConst : Integrable (fun _ : Ω => b) P := integrable_const b
  have hConstM : Integrable (fun ω => b + M n ω) P := hConst.add (hM n)
  have hRewrite :
      (∫ ω, b + M n ω + max (E n ω) 0 ∂P) =
        b + (∫ ω, M n ω ∂P) +
          (∫ ω, max (E n ω) 0 ∂P) := by
    calc
      _ = (∫ ω, b + M n ω ∂P) + (∫ ω, max (E n ω) 0 ∂P) :=
        integral_add hConstM (hE n)
      _ = b + (∫ ω, M n ω ∂P) +
          (∫ ω, max (E n ω) 0 ∂P) := by
        rw [integral_add hConst (hM n)]
        simp
  rw [hRewrite] at hCmp
  linarith [hMean n]
