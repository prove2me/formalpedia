-- Prove2me | solution 1 for CohnElkies.lowerStripPoissonMajorant_dimension_central_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/88f8ea77-5ea8-4787-885d-2adb16a2e0d1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_neg
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_integral_stripPoissonKernel
import Theorems.Thm_CohnElkies_lowerGammaScaled_poisson_product_integrable
import Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_scaled_convolution
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_riemann_le
import Theorems.Thm_CohnElkies_lowerRiemannErrorMajorant_poisson_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_mul_lowerEndpointPhase_integrable
import Theorems.Thm_CohnElkies_integral_stripPoissonKernel_mul_lowerEndpointPhase

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
    {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c) (hzero : 0 ≤ σ) (habove : σ < 1) :
    lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ 0 ≤
      ((d : ℝ) / 2) * stripBottomMass σ *
        (Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerPoissonEndpointExpectation σ) +
        lowerRiemannPoissonError σ := by
  have hbelow : -1 < σ := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hdpos)
  let ℓ : ℝ := (d : ℝ) / 2
  let A : ℝ := Real.log
    (2 * Real.pi * Real.exp 1 * c ^ 2)
  let K : ℝ → ℝ := stripPoissonKernel σ
  let q : ℝ → ℝ := lowerEndpointPhase
  let E : ℝ → ℝ := lowerRiemannErrorMajorant
  have hleft0 := lowerGammaScaled_poisson_product_integrable
    hdpos (R := c * Real.sqrt d) hbelow habove 0
  have hleft : Integrable (fun T : ℝ =>
      K T * lowerGammaBoundaryLog ℓ
        (c * Real.sqrt d) (ℓ * T)) := by
    simpa only [zero_sub, stripPoissonKernel_neg] using! hleft0
  have hk : Integrable K :=
    stripPoissonKernel_integrable hbelow habove
  have hq : Integrable (fun T : ℝ => K T * q T) :=
    stripPoissonKernel_mul_lowerEndpointPhase_integrable
      hzero habove
  have hE : Integrable (fun T : ℝ => K T * E T) :=
    lowerRiemannErrorMajorant_poisson_integrable
      hzero habove
  have hconstant := hk.const_mul (ℓ * A)
  have hphaseterm := hq.const_mul ℓ
  have hsum := hconstant.add (hphaseterm.add hE)
  have hright : Integrable (fun T : ℝ =>
      K T * (ℓ * (A + q T) + E T)) := by
    convert! hsum using 1
    ext T
    change
      K T * (ℓ * (A + q T) + E T) =
        (ℓ * A) * K T +
          (ℓ * (K T * q T) + K T * E T)
    ring
  have hmono :
      (∫ T : ℝ, K T *
        lowerGammaBoundaryLog ℓ
          (c * Real.sqrt d) (ℓ * T)) ≤
        ∫ T : ℝ, K T *
          (ℓ * (A + q T) + E T) := by
    apply integral_mono_ae hleft hright
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
      with T hT
    apply mul_le_mul_of_nonneg_left
      (lowerGammaBoundaryLog_dimension_scaled_riemann_le
        hd hc hT)
      (stripPoissonKernel_pos hbelow habove T).le
  have heval :
      (∫ T : ℝ, K T *
          (ℓ * (A + q T) + E T)) =
        ℓ * stripBottomMass σ *
          (A + lowerPoissonEndpointExpectation σ) +
            lowerRiemannPoissonError σ := by
    calc
      (∫ T : ℝ, K T *
          (ℓ * (A + q T) + E T)) =
        ∫ T : ℝ,
          (ℓ * A) * K T +
            (ℓ * (K T * q T) + K T * E T) := by
          apply integral_congr_ae
          filter_upwards [] with T
          ring
      _ =
        (∫ T : ℝ, (ℓ * A) * K T) +
          ((∫ T : ℝ, ℓ * (K T * q T)) +
            ∫ T : ℝ, K T * E T) := by
          have hfirst :=
            integral_add hconstant (hphaseterm.add hE)
          have hsecond := integral_add hphaseterm hE
          simpa only [Pi.add_apply] using!
            hfirst.trans
              (congrArg
                (fun x : ℝ =>
                  (∫ T : ℝ, (ℓ * A) * K T) + x)
                hsecond)
      _ =
        ℓ * stripBottomMass σ *
          (A + lowerPoissonEndpointExpectation σ) +
            lowerRiemannPoissonError σ := by
          rw [integral_const_mul, integral_const_mul,
            integral_stripPoissonKernel hbelow habove,
            integral_stripPoissonKernel_mul_lowerEndpointPhase
              habove]
          change
            (ℓ * A) * stripBottomMass σ +
              (ℓ * (stripBottomMass σ *
                lowerPoissonEndpointExpectation σ) +
                lowerRiemannPoissonError σ) = _
          ring
  rw [lowerStripPoissonMajorant_scaled_convolution
    hℓ (c * Real.sqrt d) σ 0]
  simp only [zero_div, zero_sub, stripPoissonKernel_neg]
  exact hmono.trans_eq heval
end CohnElkies
