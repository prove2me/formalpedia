-- Prove2me | solution 1 for CohnElkies.lowerGammaScaled_poisson_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/54850e02-3d11-4e14-8ae6-e82eadb39509

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_re
import Theorems.Thm_CohnElkies_lowerStripGammaOuter_integrable_dimension

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Integrable (fun Y : ℝ =>
      stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R
          (((d : ℝ) / 2) * Y)) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have hz :
      ((((d : ℝ) / 2) * s : ℝ) : ℂ) +
          Complex.I * ((σ * ((d : ℝ) / 2) : ℝ) : ℂ) ∈
        Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) := by
    simp only [Set.mem_preimage, Set.mem_Ioo,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, one_mul, zero_add]
    constructor
    · nlinarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
    · nlinarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  have houter := lowerStripGammaOuter_integrable_dimension
    hd (R := R) hz
  have hreal := houter.re
  have hscaled := hreal.comp_mul_left' hℓ.ne'
  have hproduct := hscaled.const_mul ((d : ℝ) / 2)
  convert! hproduct using 1
  ext Y
  change
    stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R
          (((d : ℝ) / 2) * Y) =
      ((d : ℝ) / 2) *
        (stripRegularizedHolomorphicPoissonKernel
          ((d : ℝ) / 2)
          (((((d : ℝ) / 2) * s : ℝ) : ℂ) +
            Complex.I * ((σ * ((d : ℝ) / 2) : ℝ) : ℂ))
          (((d : ℝ) / 2) * Y) *
            (lowerGammaBoundaryLog ((d : ℝ) / 2) R
              (((d : ℝ) / 2) * Y) : ℂ)).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [stripRegularizedHolomorphicPoissonKernel_re
    hℓ hbelow habove]
  have harg :
      (((d : ℝ) / 2) * s - ((d : ℝ) / 2) * Y) /
          ((d : ℝ) / 2) = s - Y := by
    field_simp [hℓ.ne']
  rw [harg]
  field_simp [hℓ.ne']
end CohnElkies
