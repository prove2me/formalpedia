-- Prove2me | solution 1 for AvramDividend.Classical.lipschitz_shifted_payoff_integrable_of_L1_difference
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:04:56.449389+00:00
-- url     : https://prove2.me/submissions/c10e357b-56b6-4865-9431-002a545aa9df

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Tactic.Ring

open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Zn Z Y : Ω → ℝ)
    (hZn : Measurable Zn) (hZ : Measurable Z)
    (hY : Measurable Y)
    (hBase : Integrable (fun ω => f (Z ω + Y ω)) P)
    (hDom : Integrable (fun ω => L * |Zn ω - Z ω|) P) :
    Integrable (fun ω => f (Zn ω + Y ω)) P := by
  have hdiff : Integrable (fun ω => f (Zn ω + Y ω) - f (Z ω + Y ω)) P := by
    refine hDom.mono ?_ ?_
    · exact ((hf.comp (hZn.add hY)).sub (hf.comp (hZ.add hY))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      have h := hLip (Zn ω + Y ω) (Z ω + Y ω)
      have e : Zn ω + Y ω - (Z ω + Y ω) = Zn ω - Z ω := by ring
      rw [e] at h
      simp only [Real.norm_eq_abs]
      exact h.trans (le_abs_self (L * |Zn ω - Z ω|))
  have := hdiff.add hBase
  refine this.congr (Filter.Eventually.of_forall (fun ω => ?_))
  simp
