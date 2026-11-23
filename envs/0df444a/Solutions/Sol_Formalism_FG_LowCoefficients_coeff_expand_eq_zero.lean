-- Prove2me | solution 1 for Formalism.FG.LowCoefficients.coeff_expand_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:11.707942+00:00
-- url     : https://prove2.me/submissions/3c67eb94-daa3-417a-8ef8-164069ca7010

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.LowCoefficients
open Formalism.G
namespace Formalism.FG.LowCoefficients
theorem _root_.solution {R : Type*} [CommRing R] {τ : Type*} (q : ℕ) (hq : q ≠ 0)
    (hq2 : 2 ≤ q) (φ : MvPowerSeries τ R) (N : ℕ) (hN : 1 ≤ N)
    (hlow : ∀ m : τ →₀ ℕ, m.degree < N → MvPowerSeries.coeff m φ = 0)
    (d : τ →₀ ℕ) (hd : d.degree = N) : MvPowerSeries.coeff d (MvPowerSeries.expand q hq φ) = 0 := by

  classical
  by_cases hdiv : ∀ i, q ∣ d i
  · let m : τ →₀ ℕ := d.mapRange (fun k => k / q) (by simp)
    have hdm : d = q • m := by
      ext i
      simp [m, Nat.mul_div_cancel' (hdiv i)]
    have hdeg : d.degree = q * m.degree := by
      rw [hdm, map_nsmul, smul_eq_mul]
    rw [hdm, MvPowerSeries.coeff_expand_smul]
    apply hlow
    have h1 : q * m.degree = N := by rw [← hdeg, hd]
    have h2 : 0 < m.degree := by
      rcases Nat.eq_zero_or_pos m.degree with h | h
      · rw [h, mul_zero] at h1
        omega
      · exact h
    nlinarith
  · push_neg at hdiv
    obtain ⟨i, hi⟩ := hdiv
    exact MvPowerSeries.coeff_expand_of_not_dvd q hq φ hi
end Formalism.FG.LowCoefficients
