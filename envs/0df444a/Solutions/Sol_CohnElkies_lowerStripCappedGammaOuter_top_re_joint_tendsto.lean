-- Prove2me | solution 1 for CohnElkies.lowerStripCappedGammaOuter_top_re_joint_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/83728e33-2c08-411e-96a3-d9f2c402ef21

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_continuous
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_re_dimension
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_dimension_abs_le_linear
import Theorems.Thm_CohnElkies_harmonic_upper_joint_tendsto_zero

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Tendsto
      (fun z : ℂ =>
        (lowerStripCappedGammaOuter
          ((d : ℝ) / 2) R D z).re)
      (𝓝[Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)]
          ((s : ℂ) +
            Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)))
      (𝓝 (0 : ℝ)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  let U : Set ℂ := Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ := (s : ℂ) + Complex.I * (ℓ : ℂ)
  have hℓ : 0 < ℓ := half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A, hA, hbound⟩ :=
    lowerGammaBoundaryCapped_dimension_abs_le_linear hd R D
  have hcontinuous :=
    lowerGammaBoundaryCapped_continuous hℓ R D
  have hpoisson := harmonic_upper_joint_tendsto_zero
    hℓ hcontinuous hA hbound s
  have heq :
      (fun z : ℂ =>
        (lowerStripCappedGammaOuter ℓ R D z).re) =ᶠ[𝓝[U] z₀]
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            lowerGammaBoundaryCapped ℓ R D
              (z.re - ℓ * T)) := by
    filter_upwards [self_mem_nhdsWithin]
      with z hz
    have hbelow : -1 < z.im / ℓ := by
      apply (lt_div_iff₀ hℓ).2
      simpa using! hz.1
    have habove : z.im / ℓ < 1 := by
      apply (div_lt_iff₀ hℓ).2
      simpa using! hz.2
    have hrepr :
        (z.re : ℂ) + Complex.I *
          (((z.im / ℓ * ℓ : ℝ) : ℂ)) = z := by
      apply Complex.ext
      · simp
      · simp [hℓ.ne']
    rw [← hrepr]
    simpa [ℓ, hℓ.ne'] using!
      (lowerStripCappedGammaOuter_re_dimension
        (R := R) (D := D) hd hbelow habove z.re)
  have hresult := hpoisson.congr' heq.symm
  simpa [ℓ, U, z₀] using! hresult
end CohnElkies
