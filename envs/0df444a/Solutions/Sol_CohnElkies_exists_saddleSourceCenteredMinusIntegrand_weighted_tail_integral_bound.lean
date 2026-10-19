-- Prove2me | solution 1 for CohnElkies.exists_saddleSourceCenteredMinusIntegrand_weighted_tail_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/c19d3f69-6523-476a-b3da-e843f650aef0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceCenteredMinusIntegrand_norm
import Theorems.Thm_CohnElkies_saddleSourceCenteredMinusIntegrand_integrable
import Theorems.Thm_CohnElkies_exists_minusPolynomial_uniform_weighted_bound
import Theorems.Thm_CohnElkies_saddleSource_weighted_tail_integral_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ u : ℝ, 1 + ε / 4 ≤ u →
          ∀ v R : ℝ,
            Integrable (fun T : ℝ =>
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T)) →
            (∫ T : ℝ in saddleGaussianTailSet R,
              ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖) ≤
              C * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
                (∫ T : ℝ in saddleGaussianTailSet R,
                  saddleGaussianTailWeight T *
                    Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  obtain ⟨C, hC, hpoly⟩ :=
    exists_minusPolynomial_uniform_weighted_bound hε
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ u hu v R hweighted
  have hu' : -1 < u := by linarith
  apply saddleSource_weighted_tail_integral_le
    (saddleSourceCenteredMinusIntegrand_integrable
      hε hℓ hu' horder v) hweighted
  intro T hT
  rw [saddleSourceCenteredMinusIntegrand_norm
    hε hℓ hu' horder]
  have hp := hpoly u hu T
  unfold saddleGaussianTailWeight
  calc
    Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ ≤
      Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        (C * (1 + |T| ^ 3) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖) := by
        gcongr
    _ = (C * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖) *
        ((1 + |T| ^ 3) *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
        ring
end CohnElkies
