-- Prove2me | solution 1 for CohnElkies.exp_integral_upperGammaCenteredTruncatedKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/11ad0c95-bfff-468e-9558-04260b42a434

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaEuler_centered_ratio
import Theorems.Thm_CohnElkies_exp_integral_upperGammaCenteredTruncatedKernel_eq_product

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
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) {n : ℕ} (hn : 0 < n) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperGammaCenteredTruncatedKernel ℓ η T n a) =
      (Complex.GammaSeq
          (((ℓ * η / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) n /
        Complex.GammaSeq
          ((ℓ * η / 2 : ℝ) : ℂ) n) *
        Complex.exp
          (Complex.I *
            (((ℓ * T / 2 *
              (Real.log (n : ℝ) -
                ∑ k ∈ Finset.range (n + 1),
                  (ℓ * η / 2 + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
  classical
  let m : ℝ := ℓ * η / 2
  let b : ℝ := ℓ * T / 2
  have hm : 0 < m := by
    try dsimp [m]
    positivity
  have hproduct :
      Complex.exp
        (∫ a : ℝ in Ioi 0,
          upperGammaCenteredTruncatedKernel ℓ η T n a) =
        (∏ k ∈ Finset.range (n + 1),
          (((m : ℂ) + (k : ℂ)) /
            ((m : ℂ) - Complex.I * (b : ℂ) +
              (k : ℂ)))) *
          Complex.exp
            (-Complex.I *
              (((b *
                (∑ k ∈ Finset.range (n + 1),
                  (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
    simpa [m, b] using!
      exp_integral_upperGammaCenteredTruncatedKernel_eq_product
        hℓ hη T n
  have hphase :
      Complex.exp
        (-Complex.I *
          (((b *
            (∑ k ∈ Finset.range (n + 1),
              (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) =
        Complex.exp
          (-Complex.I *
            ((b * Real.log (n : ℝ) : ℝ) : ℂ)) *
          Complex.exp
            (Complex.I *
              (((b *
                (Real.log (n : ℝ) -
                  ∑ k ∈ Finset.range (n + 1),
                    (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  change
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperGammaCenteredTruncatedKernel ℓ η T n a) =
      (Complex.GammaSeq
          ((m : ℂ) - Complex.I * (b : ℂ)) n /
        Complex.GammaSeq (m : ℂ) n) *
        Complex.exp
          (Complex.I *
            (((b *
              (Real.log (n : ℝ) -
                ∑ k ∈ Finset.range (n + 1),
                  (m + (k : ℝ))⁻¹) : ℝ) : ℂ)))
  calc
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperGammaCenteredTruncatedKernel ℓ η T n a) =
        (∏ k ∈ Finset.range (n + 1),
          (((m : ℂ) + (k : ℂ)) /
            ((m : ℂ) - Complex.I * (b : ℂ) +
              (k : ℂ)))) *
          Complex.exp
            (-Complex.I *
              (((b *
                (∑ k ∈ Finset.range (n + 1),
                  (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := hproduct
    _ = (Complex.exp
          (-Complex.I *
            ((b * Real.log (n : ℝ) : ℝ) : ℂ)) *
          (∏ k ∈ Finset.range (n + 1),
            (((m : ℂ) + (k : ℂ)) /
              ((m : ℂ) - Complex.I * (b : ℂ) +
                (k : ℂ))))) *
          Complex.exp
            (Complex.I *
              (((b *
                (Real.log (n : ℝ) -
                  ∑ k ∈ Finset.range (n + 1),
                    (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
      rw [hphase]
      ring
    _ = (Complex.GammaSeq
          ((m : ℂ) - Complex.I * (b : ℂ)) n /
        Complex.GammaSeq (m : ℂ) n) *
        Complex.exp
          (Complex.I *
            (((b *
              (Real.log (n : ℝ) -
                ∑ k ∈ Finset.range (n + 1),
                  (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
      rw [upperGammaEuler_centered_ratio hm b hn]
end CohnElkies
