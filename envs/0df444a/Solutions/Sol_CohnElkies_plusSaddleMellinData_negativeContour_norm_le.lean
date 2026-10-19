-- Prove2me | solution 1 for CohnElkies.plusSaddleMellinData_negativeContour_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/e3547d7c-8d73-4b12-8b4b-a43681fdb2ea

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperNegativeContour_gamma_mul_shellExponential_le
import Theorems.Thm_CohnElkies_norm_plusPolynomial_negativeContour_le
import Theorems.Thm_CohnElkies_saddleNegativeContour_piExponential_norm

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (s : ℝ) :
    ‖plusSaddleMellinData ε ℓ
        ((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I)‖ ≤
      saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMajorant ε s := by
  let z : ℂ := (saddleTaylorContour N : ℂ) +
    (s : ℂ) * Complex.I
  let q : ℂ := Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)
  have hfactor :=
    upperNegativeContour_gamma_mul_shellExponential_le
      hε hεsmall hℓ N hN horder hmargin s
  have hpoly := norm_plusPolynomial_negativeContour_le
    (ε := ε) hℓ N hN s
  have hpi := saddleNegativeContour_piExponential_norm
    ℓ N s
  change ‖plusSaddleMellinData ε ℓ z‖ ≤ _
  unfold plusSaddleMellinData saddleMellinEnvelope
  change
    ‖(Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
        Complex.Gamma (z / 2) *
          Complex.exp ((ℓ : ℂ) * mellinShellPhase ε q)) *
            plusPolynomial ε q‖ ≤ _
  calc
    ‖(Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
        Complex.Gamma (z / 2) *
          Complex.exp ((ℓ : ℂ) * mellinShellPhase ε q)) *
            plusPolynomial ε q‖ =
      ‖Complex.exp
        (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2)‖ *
        ‖Complex.Gamma (z / 2) *
          Complex.exp ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
            ‖plusPolynomial ε q‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul]
      ring
    _ ≤ Real.exp
        ((ℓ - saddleTaylorContour N) *
          Real.log Real.pi / 2) *
        (Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (saddleNegativeContourOrdinate ℓ N)) *
          ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            Real.exp (2 * ε * Real.log 2) *
              Real.exp (-ε * Real.pi * |s|))) *
          (27 * (1 + |beta ε|) * (1 + |s|) ^ 3) := by
      have hfactor' :
          ‖Complex.Gamma (z / 2) *
            Complex.exp ((ℓ : ℂ) * mellinShellPhase ε q)‖ ≤
            Real.exp
              (ℓ * realHyperbolicShellPhase ε
                (saddleNegativeContourOrdinate ℓ N)) *
              ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
                Real.exp (2 * ε * Real.log 2) *
                  Real.exp (-ε * Real.pi * |s|)) := by
        simpa [z, q] using! hfactor
      have hpoly' :
          ‖plusPolynomial ε q‖ ≤
            27 * (1 + |beta ε|) * (1 + |s|) ^ 3 := by
        simpa [z, q] using! hpoly
      have hpi' :
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ =
            Real.exp
              ((ℓ - saddleTaylorContour N) *
                Real.log Real.pi / 2) := by
        simpa [z] using! hpi
      rw [hpi']
      gcongr
    _ = saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMajorant ε s := by
      unfold saddleNegativeMellinMajorantCoefficient
        saddleNegativeFrequencyMajorant
      ring
end CohnElkies
