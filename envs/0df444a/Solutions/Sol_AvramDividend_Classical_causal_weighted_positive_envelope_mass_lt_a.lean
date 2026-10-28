-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_positive_envelope_mass_lt_a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:16:00.958195+00:00
-- url     : https://prove2.me/submissions/285ea0a2-09fd-41c2-a33b-6fdbe0a77e6e

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The positive drift-plus-kernel envelope inherits the same strict
weighted mass threshold as the absolute drift and kernel components. -/
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (hw : 0 < w)
    (hKi : IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) volume ∧
    (∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * (|β| + K t) ∂volume) < a := by
  obtain ⟨hExp, hExpEq⟩ :=
    positive_laplace_constant_reference w hw
  have hKabs : IntegrableOn
      (fun t : ℝ => |K t| * Real.exp (-w * t))
      (Ioi (0 : ℝ)) volume := by
    have hn := hKi.norm
    change Integrable (fun t : ℝ => |K t| * Real.exp (-w * t))
      (volume.restrict (Ioi (0 : ℝ)))
    convert hn using 1
    funext t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    ring
  have hβabs : IntegrableOn
      (fun t : ℝ => |β| * Real.exp (-w * t))
      (Ioi (0 : ℝ)) volume := by
    change Integrable (fun t : ℝ => |β| * Real.exp (-w * t))
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [neg_mul] using hExp.const_mul |β|
  have hfull : IntegrableOn
      (fun t : ℝ => Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) volume := by
    have hb := (hExp.const_mul |β|).add hKi
    change Integrable
      (fun t : ℝ => Real.exp (-w * t) * (|β| + K t))
      (volume.restrict (Ioi (0 : ℝ)))
    have hfun :
        ((fun t : ℝ => |β| * Real.exp (-(w * t))) +
          (fun t : ℝ => Real.exp (-w * t) * K t)) =
        (fun t : ℝ => Real.exp (-w * t) * (|β| + K t)) := by
      funext t
      simp only [Pi.add_apply, neg_mul]
      ring
    rw [hfun] at hb
    exact hb
  have hmajor := hβabs.add hKabs
  have hle : (∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * (|β| + K t) ∂volume) ≤
      (∫ t in Ioi (0 : ℝ),
        |β| * Real.exp (-w * t) +
          |K t| * Real.exp (-w * t) ∂volume) := by
    apply integral_mono hfull hmajor
    intro t
    calc
      Real.exp (-w * t) * (|β| + K t) ≤
        Real.exp (-w * t) * (|β| + |K t|) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_right (le_abs_self (K t)) |β|)
            (Real.exp_nonneg _)
      _ = |β| * Real.exp (-w * t) +
            |K t| * Real.exp (-w * t) := by ring
  refine ⟨hfull, ?_⟩
  calc
    (∫ t in Ioi (0 : ℝ),
        Real.exp (-w * t) * (|β| + K t) ∂volume) ≤
      (∫ t in Ioi (0 : ℝ),
        |β| * Real.exp (-w * t) +
          |K t| * Real.exp (-w * t) ∂volume) := hle
    _ = |β| / w +
        (∫ t in Ioi (0 : ℝ),
          |K t| * Real.exp (-w * t) ∂volume) := by
      have heq :
          (∫ t in Ioi (0 : ℝ),
            Real.exp (-w * t) ∂volume) = 1 / w := by
        simpa only [neg_mul] using hExpEq
      rw [integral_add hβabs hKabs, integral_const_mul, heq]
      ring
    _ < a := hsmall
