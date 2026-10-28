-- Prove2me | solution 1 for AvramDividend.Classical.bv_volterra_transform_scalar_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:29:31.221319+00:00
-- url     : https://prove2.me/submissions/d3f742c5-0fa3-45b6-98a0-0c213fe9ae3c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Rearrange the BV exponent into the finite-activity Volterra transform. -/
theorem solution
    (d q rate J ψ θ : ℝ) (hθ : θ ≠ 0) (hden : ψ - q ≠ 0)
    (hψ : ψ = d * θ - rate + J) :
    d * (ψ - q)⁻¹ = θ⁻¹ +
      (q + rate) * ((ψ - q)⁻¹ / θ) -
      J * ((ψ - q)⁻¹ / θ) := by
  field_simp [hθ, hden]
  linarith [hψ]
