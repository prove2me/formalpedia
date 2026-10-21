-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_preserves_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:53:44.515975+00:00
-- url     : https://prove2.me/submissions/bd2b2137-f816-4fce-9c63-f70901ce5692

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable (fun ω => f (x + X.X t ω)) P) :
    ∀ x y : ℝ,
      |(∫ ω, f (x + X.X t ω) ∂P) -
        (∫ ω, f (y + X.X t ω) ∂P)| ≤ L * |x - y| := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro x y
  have hdif : Integrable
      (fun ω => f (x + X.X t ω) - f (y + X.X t ω)) P :=
    (hInt x).sub (hInt y)
  have hpath (ω : Ω) :
      |f (x + X.X t ω) - f (y + X.X t ω)| ≤
        L * |x - y| := by
    have h := hLip (x + X.X t ω) (y + X.X t ω)
    have hshift :
        (x + X.X t ω) - (y + X.X t ω) = x - y := by
      ring
    rw [hshift] at h
    exact h
  have hup : ∀ᵐ ω ∂P,
      f (x + X.X t ω) - f (y + X.X t ω) ≤
        L * |x - y| := by
    filter_upwards [] with ω
    exact (abs_le.mp (hpath ω)).2
  have hlow : ∀ᵐ ω ∂P,
      -(L * |x - y|) ≤
        f (x + X.X t ω) - f (y + X.X t ω) := by
    filter_upwards [] with ω
    exact (abs_le.mp (hpath ω)).1
  have hupper :
      (∫ ω, f (x + X.X t ω) - f (y + X.X t ω) ∂P) ≤
        L * |x - y| := by
    have h :=
      MeasureTheory.integral_mono_ae hdif
        (integrable_const (L * |x - y|)) hup
    simpa using h
  have hlower :
      -(L * |x - y|) ≤
        (∫ ω, f (x + X.X t ω) - f (y + X.X t ω) ∂P) := by
    have h :=
      MeasureTheory.integral_mono_ae
        (integrable_const (-(L * |x - y|))) hdif hlow
    simpa using h
  have hint :
      (∫ ω, f (x + X.X t ω) - f (y + X.X t ω) ∂P) =
        (∫ ω, f (x + X.X t ω) ∂P) -
        (∫ ω, f (y + X.X t ω) ∂P) :=
    integral_sub (hInt x) (hInt y)
  rw [hint] at hupper hlower
  exact abs_le.mpr ⟨hlower, hupper⟩
