-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryCapped_central_poisson_shift_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/0635f036-b275-43cb-9408-e8e5d39ac861

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_re
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_integrable_dimension

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel 0 T *
        lowerGammaBoundaryCapped ((d : ℝ) / 2) R D
          (s - ((d : ℝ) / 2) * T)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ := half_pos (Nat.cast_pos.mpr hd)
  let z : ℂ := (s : ℂ) +
    Complex.I * ((0 * ℓ : ℝ) : ℂ)
  have hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ := by
    try dsimp [z]
    simp only [Set.mem_preimage, Set.mem_Ioo,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re,
      zero_mul, one_mul, zero_add]
    constructor <;> linarith
  have houter := lowerStripCappedGammaOuter_integrable_dimension
    hd (R := R) (D := D) hz
  have hreal := houter.re
  have htranslated := hreal.comp_sub_left s
  have hscaled := htranslated.comp_mul_left' hℓ.ne'
  have hproduct := hscaled.const_mul ℓ
  convert! hproduct using 1
  ext T
  change
    stripPoissonKernel 0 T *
      lowerGammaBoundaryCapped ℓ R D (s - ℓ * T) =
      ℓ *
        (stripRegularizedHolomorphicPoissonKernel ℓ z
          (s - ℓ * T) *
            (lowerGammaBoundaryCapped ℓ R D
              (s - ℓ * T) : ℂ)).re
  rw [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  try dsimp [z]
  rw [stripRegularizedHolomorphicPoissonKernel_re
    hℓ (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1)]
  have harg : (s - (s - ℓ * T)) / ℓ = T := by
    field_simp [hℓ.ne']
    ring
  rw [harg]
  field_simp [hℓ.ne']
end CohnElkies
