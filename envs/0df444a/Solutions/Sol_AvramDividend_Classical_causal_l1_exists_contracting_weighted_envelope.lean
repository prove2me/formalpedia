-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_exists_contracting_weighted_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:36:06.489011+00:00
-- url     : https://prove2.me/submissions/b3db9137-5257-44e9-89aa-83d7c1d07490

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_volterra_exponential_kernel_weight_small
import Theorems.Thm_AvramDividend_Classical_causal_l1_exponential_damping_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_positive_envelope_normalized_lt_one

open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Select a damping weight with integrable, subunit causal envelope mass. -/
theorem solution
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ w : ℝ, 0 < w ∧
      IntegrableOn (fun t : ℝ =>
        a⁻¹ * Real.exp (-w * t) * (|β| + K t))
        (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ),
        a⁻¹ * Real.exp (-w * t) * (|β| + K t) ∂volume) < 1 := by
  obtain ⟨w, hw, hsmall⟩ :=
    causal_volterra_exponential_kernel_weight_small K a β ha hK
  have hKi := causal_l1_exponential_damping_integrable K w hw hK
  obtain ⟨hE, hMass⟩ :=
    causal_weighted_positive_envelope_normalized_lt_one
      K a β w ha hw hKi hsmall
  exact ⟨w, hw, hE, hMass⟩
