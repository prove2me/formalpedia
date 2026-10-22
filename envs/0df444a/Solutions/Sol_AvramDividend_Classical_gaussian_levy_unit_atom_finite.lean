-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_unit_atom_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:21:08.804664+00:00
-- url     : https://prove2.me/submissions/447b669a-202b-4630-ab1b-23aa4fa2a9c3

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Lévy truncated-square integrability forces finite jump intensity
at the unit positive jump magnitude, retaining possible atoms. -/
theorem solution (μ : Measure ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    μ ({1} : Set ℝ) < ⊤ := by
  let F : ℝ → ENNReal :=
    fun z => ENNReal.ofReal (min 1 (z ^ 2))
  have hsingle : (∫⁻ z in ({1} : Set ℝ), F z ∂μ) =
      μ ({1} : Set ℝ) := by
    calc
      _ = ∫⁻ z in ({1} : Set ℝ), (1 : ENNReal) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards
          [ae_restrict_mem (μ := μ) (measurableSet_singleton (1 : ℝ))]
          with z hz
        have heq : z = 1 := by simpa only [mem_singleton_iff] using hz
        subst z
        simp [F]
      _ = μ ({1} : Set ℝ) := by simp
  have hsub : ({1} : Set ℝ) ⊆ Ioi (0 : ℝ) := by
    intro z hz
    have heq : z = 1 := by simpa only [mem_singleton_iff] using hz
    subst z
    norm_num
  have hmono : (∫⁻ z in ({1} : Set ℝ), F z ∂μ) ≤
      (∫⁻ z in Ioi (0 : ℝ), F z ∂μ) :=
    lintegral_mono_set hsub
  rw [hsingle] at hmono
  exact lt_of_le_of_lt hmono hlevy
