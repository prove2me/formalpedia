-- Prove2me | solution 1 for CohnElkies.eventually_saddleGaussianOuterPhi_uniform_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/30962e04-232f-4330-8e1e-0da2966ee4d0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleGaussianOuterPhi_uniform

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {B Q c δ₀ K : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hc : 0 < c)
    (hδ₀ : 0 ≤ δ₀) (hK : 0 ≤ K) :
    ∀ κ : ℝ, 0 < κ →
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, δ₀ ≤ δ →
          K * Real.sqrt ℓ *
              Real.exp (((B + 1) / 2) * δ) *
              (2 + δ) ^ 4 *
              Real.exp
                (-c * ℓ * Q * Real.exp (B * δ)) < κ := by
  intro κ hκ
  rcases hK.eq_or_lt with hKzero | hKpos
  · subst K
    filter_upwards [] with ℓ
    intro δ hδ
    simpa using! hκ
  · have hlimit :=
      eventually_saddleGaussianOuterPhi_uniform
        hB hQ hc hδ₀ (κ / K)
        (div_pos hκ hKpos)
    filter_upwards [hlimit] with ℓ hℓ
    intro δ hδ
    have hδnonnegative : 0 ≤ δ := hδ₀.trans hδ
    have hη : 0 < 2 + δ := by linarith
    have hpower :
        (2 + δ) ^ 4 =
          Real.exp (4 * Real.log (2 + δ)) := by
      calc
        (2 + δ) ^ 4 =
            (Real.exp (Real.log (2 + δ))) ^ 4 := by
              rw [Real.exp_log hη]
        _ = Real.exp (4 * Real.log (2 + δ)) := by
              rw [← Real.exp_nat_mul]
              norm_num
    have hproduct :
        Real.exp (((B + 1) / 2) * δ) *
            Real.exp (4 * Real.log (2 + δ)) *
            Real.exp
              (-c * ℓ * Q * Real.exp (B * δ)) =
          Real.exp (saddleGaussianOuterPhi B Q c ℓ δ) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold saddleGaussianOuterPhi
      ring
    have hrewrite :
        K * Real.sqrt ℓ *
            Real.exp (((B + 1) / 2) * δ) *
            (2 + δ) ^ 4 *
            Real.exp
              (-c * ℓ * Q * Real.exp (B * δ)) =
          K *
            (Real.sqrt ℓ *
              Real.exp (saddleGaussianOuterPhi B Q c ℓ δ)) := by
      rw [hpower]
      calc
        K * Real.sqrt ℓ *
            Real.exp (((B + 1) / 2) * δ) *
            Real.exp (4 * Real.log (2 + δ)) *
            Real.exp
              (-c * ℓ * Q * Real.exp (B * δ)) =
          K * Real.sqrt ℓ *
            (Real.exp (((B + 1) / 2) * δ) *
              Real.exp (4 * Real.log (2 + δ)) *
              Real.exp
                (-c * ℓ * Q * Real.exp (B * δ))) := by
                ring
        _ = K *
            (Real.sqrt ℓ *
              Real.exp (saddleGaussianOuterPhi B Q c ℓ δ)) := by
            rw [hproduct]
            ring
    rw [hrewrite]
    calc
      K *
          (Real.sqrt ℓ *
            Real.exp (saddleGaussianOuterPhi B Q c ℓ δ)) <
        K * (κ / K) :=
          mul_lt_mul_of_pos_left (hℓ δ hδ) hKpos
      _ = κ := by field_simp
end CohnElkies
