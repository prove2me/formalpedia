-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_envelope_pointwise_le_mass_div_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:13:19.556393+00:00
-- url     : https://prove2.me/submissions/67dda31f-faa1-4e26-9537-d47bfeddc695

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_antitone_positive_kernel_mass_lower_bound
import Theorems.Thm_AvramDividend_Classical_causal_weighted_nonnegative_kernel_envelope_antitone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The positive weighted Volterra envelope is bounded by its accumulated mass per unit time. -/
theorem solution
    (K : ℝ → ℝ) (w β a ρ x : ℝ) (ha : 0 < a) (hw : 0 ≤ w)
    (hx : 0 < x) (hanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hK : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ K t)
    (hint : IntervalIntegrable
      (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t)) volume 0 x)
    (hmass : (∫ t in (0 : ℝ)..x,
      a⁻¹ * Real.exp (-w * t) * (|β| + K t)) ≤ ρ) :
    a⁻¹ * Real.exp (-w * x) * (|β| + K x) ≤ ρ / x := by
  let E : ℝ → ℝ := fun t =>
    a⁻¹ * Real.exp (-w * t) * (|β| + K t)
  have heAnti : AntitoneOn E (Ioi (0 : ℝ)) := by
    intro s hs t ht hst
    change a⁻¹ * Real.exp (-w * t) * (|β| + K t) ≤
      a⁻¹ * Real.exp (-w * s) * (|β| + K s)
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left
        ((AvramDividend.Classical.causal_weighted_nonnegative_kernel_envelope_antitone
          K w β hw hanti hK) hs ht hst)
        (inv_nonneg.mpr ha.le))
  have hpoint :=
    AvramDividend.Classical.antitone_positive_kernel_mass_lower_bound
      E heAnti x hx hint
  change E x ≤ ρ / x
  apply (le_div_iff₀ hx).2
  calc
    E x * x = x * E x := mul_comm _ _
    _ ≤ ∫ t in (0 : ℝ)..x, E t := hpoint
    _ ≤ ρ := hmass
