-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_positive_envelope_normalized_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:38:19.669183+00:00
-- url     : https://prove2.me/submissions/6d7cc3be-ed38-4d46-abae-44adf6c7660a

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_weighted_positive_envelope_mass_lt_a

open AvramDividend.Classical MeasureTheory Set
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hKi : IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    IntegrableOn (fun t : ℝ =>
      a⁻¹ * Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) volume ∧
    (∫ t in Ioi (0 : ℝ),
      a⁻¹ * Real.exp (-w * t) * (|β| + K t) ∂volume) < 1 := by
  obtain ⟨hI, hlt⟩ :=
    AvramDividend.Classical.causal_weighted_positive_envelope_mass_lt_a K a β w hw hKi hsmall
  have hfun : (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t)) =
      fun t => a⁻¹ * (Real.exp (-w * t) * (|β| + K t)) := by
    funext t; ring
  rw [hfun]
  refine ⟨hI.const_mul a⁻¹, ?_⟩
  rw [integral_const_mul]
  rw [inv_mul_lt_one₀ ha]
  exact hlt
