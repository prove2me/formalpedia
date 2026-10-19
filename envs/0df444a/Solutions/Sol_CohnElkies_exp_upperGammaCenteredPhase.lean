-- Prove2me | solution 1 for CohnElkies.exp_upperGammaCenteredPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/9f740e7b-8887-415f-aa75-98514709e4a9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_saddleEulerHarmonicCorrection
import Theorems.Thm_CohnElkies_tendsto_integral_upperGammaCenteredTruncatedKernel
import Theorems.Thm_CohnElkies_exp_integral_upperGammaCenteredTruncatedKernel

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
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Complex.exp (upperGammaCenteredPhase ℓ η T) =
      (Complex.Gamma
          (((ℓ * η / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) /
        (Real.Gamma (ℓ * η / 2) : ℂ)) *
        Complex.exp
          (Complex.I *
            ((ℓ * T / 2 *
              saddleDigamma (ℓ * η / 2) : ℝ) : ℂ)) := by
  classical
  let m : ℝ := ℓ * η / 2
  let b : ℝ := ℓ * T / 2
  have hm : 0 < m := by
    try dsimp [m]
    positivity
  have hden : Complex.Gamma (m : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos
      (by simpa using! hm)
  have hgamma :
      Tendsto
        (fun n : ℕ =>
          Complex.GammaSeq
              ((m : ℂ) - Complex.I * (b : ℂ)) n /
            Complex.GammaSeq (m : ℂ) n)
        atTop
        (𝓝 (Complex.Gamma
              ((m : ℂ) - Complex.I * (b : ℂ)) /
            Complex.Gamma (m : ℂ))) := by
    exact
      (Complex.GammaSeq_tendsto_Gamma
        ((m : ℂ) - Complex.I * (b : ℂ))).div
          (Complex.GammaSeq_tendsto_Gamma (m : ℂ))
          hden
  have hcorrection :
      Tendsto
        (fun n : ℕ =>
          Complex.exp
            (Complex.I *
              (((b *
                (Real.log (n : ℝ) -
                  ∑ k ∈ Finset.range (n + 1),
                    (m + (k : ℝ))⁻¹) : ℝ) : ℂ))))
        atTop
        (𝓝
          (Complex.exp
            (Complex.I *
              ((b * saddleDigamma m : ℝ) : ℂ)))) := by
    have hreal :=
      (tendsto_saddleEulerHarmonicCorrection hm).const_mul b
    have hcomplex := hreal.ofReal
    have himag := hcomplex.const_mul Complex.I
    simpa only [Function.comp_apply] using! himag.cexp
  have hright := hgamma.mul hcorrection
  have hleft :=
    (tendsto_integral_upperGammaCenteredTruncatedKernel
      hℓ hη T).cexp
  have hfinite :
      (fun n : ℕ =>
        Complex.exp
          (∫ a : ℝ in Ioi 0,
            upperGammaCenteredTruncatedKernel ℓ η T n a)) =ᶠ[atTop]
      (fun n : ℕ =>
        (Complex.GammaSeq
            ((m : ℂ) - Complex.I * (b : ℂ)) n /
          Complex.GammaSeq (m : ℂ) n) *
          Complex.exp
            (Complex.I *
              (((b *
                (Real.log (n : ℝ) -
                  ∑ k ∈ Finset.range (n + 1),
                    (m + (k : ℝ))⁻¹) : ℝ) : ℂ)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)]
      with n hn
    simpa [m, b] using!
      exp_integral_upperGammaCenteredTruncatedKernel
        hℓ hη T hn
  have hmatch :=
    Filter.Tendsto.congr' hfinite.symm hright
  have hidentity := tendsto_nhds_unique hleft hmatch
  rw [Complex.Gamma_ofReal] at hidentity
  exact hidentity
end CohnElkies
