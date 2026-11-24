-- Prove2me | solution 1 for Formalism.G0.det_quotient_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:46.575977+00:00
-- url     : https://prove2.me/submissions/9d053ede-6dd7-407e-beed-e6e081dc0389

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal
import Theorems.Thm_Formalism_G0_DetQuotValP_substS_det_all
import Theorems.Thm_Formalism_G0_DetQuotValP_not_dvd_detX
import Theorems.Thm_Formalism_G0_DetQuotValP_not_dvd_substS_det
import Theorems.Thm_Formalism_G0_DetQuotValP_sum_cov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.G0.DetQuotValP
namespace Formalism.G0
theorem _root_.solution : Formalism.G0.DetQuotVal := by
  intro K ι _ _ _ r vec S' A d H m' th hA hv _ hle hval L _ _ g
  have h := hval L g
  rw [sum_cov vec S' A hv d m'] at h
  set c := ∑ i ∈ S'.filter (fun i => vec i = false), d i
  simp only [map_mul, map_pow] at h ⊢
  set p : MvPolynomial (ι × Fin r) (Polynomial L) := MvPolynomial.C Polynomial.X with hpdef
  have hp : Prime p := (MvPolynomial.prime_C_iff _).mpr Polynomial.prime_X
  have hnd : ∀ (U : MvPolynomial (ι × Fin r) (Polynomial L)), ¬ p ∣ U → ∀ n, p ^ n ∣ U ^ m' *
      substS (K := K) vec S' g H → p ^ n ∣ substS (K := K) vec S' g H := by
    intro U hU n hn
    exact hp.pow_dvd_of_dvd_mul_left n (fun e => hU (hp.dvd_of_dvd_pow e)) hn
  by_cases hall : 1 ≤ r ∧ ∀ l, A l ∈ S'
  · rw [substS_det_all hall.1 vec S' A hv hall.2 g, mul_pow, mul_assoc] at h
    rw [show th + c = m' + (th - m' + c) by omega, pow_add] at h
    have h' := (mul_dvd_mul_iff_left (pow_ne_zero m' hp.ne_zero)).mp h
    exact hnd _ (not_dvd_detX A hA) _ h'
  · have hnot : ¬ p ∣ substS (K := K) vec S' g (detLetters A) := by
      by_cases hr : 1 ≤ r
      · exact not_dvd_substS_det hr vec S' A hA hv (fun x => hall ⟨hr, x⟩) g
      · have hr0 : r = 0 := by omega
        subst hr0
        have : detLetters (K := K) A = 1 := Matrix.det_fin_zero
        rw [this, map_one]
        exact hp.not_dvd_one
    exact (pow_dvd_pow p (by omega)).trans (hnd _ hnot _ h)
end Formalism.G0
