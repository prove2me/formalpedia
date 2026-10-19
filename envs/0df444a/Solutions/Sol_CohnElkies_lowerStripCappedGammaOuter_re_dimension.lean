-- Prove2me | solution 1 for CohnElkies.lowerStripCappedGammaOuter_re_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/f7da54b4-6690-4358-b25d-8a21f22d01c0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_integrable_dimension
import Theorems.Thm_CohnElkies_stripRegularizedOuter_re

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
    {d : ℕ} (hd : 0 < d) {σ R D : ℝ}
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    (lowerStripCappedGammaOuter ((d : ℝ) / 2) R D
      ((s : ℂ) + Complex.I *
        ((σ * ((d : ℝ) / 2) : ℝ) : ℂ))).re =
      ∫ T : ℝ, stripPoissonKernel σ T *
        lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D
          (s - ((d : ℝ) / 2) * T) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have hz :
      ((s : ℂ) + Complex.I *
        ((σ * ((d : ℝ) / 2) : ℝ) : ℂ)) ∈
        Complex.im ⁻¹'
          Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) := by
    simp only [Set.mem_preimage, Set.mem_Ioo,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, one_mul, zero_add]
    constructor
    · nlinarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
    · nlinarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  unfold lowerStripCappedGammaOuter
  exact stripRegularizedOuter_re hℓ hσbelow hσabove s
    (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
    (lowerStripCappedGammaOuter_integrable_dimension
      hd (R := R) (D := D) hz)
end CohnElkies
