-- Prove2me | solution 1 for Formalism.HC.Der.kc_below_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:06:08.980785+00:00
-- url     : https://prove2.me/submissions/762b8376-46b3-4cfb-8668-4a23f9128418

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
import Theorems.Thm_Formalism_HC_Der_kc_exists_prime
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_HC_Der_kc_cc_not_mem
import Theorems.Thm_Formalism_HC_Der_kc_gal_conj
import Theorems.Thm_Formalism_HC_Der_kc_restrict_mem_Psi
import Theorems.Thm_Formalism_HC_Der_kc_two_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
variable (C : HostCore H)
include C
namespace Formalism.HC.Der
theorem _root_.solution (P : Ideal (𝓞 H.E)) [P.IsPrime] (hm : ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P) :
    kcBelow H P ≠ kcBelow H (H.conj • P) := by
  have := H.galois
  intro heq
  have hn0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' (by
    rintro h0
    have := H.QS_coprime
    rw [h0, zero_mul, Nat.coprime_zero_right] at this
    have h2 := kc_two_dvd H
    rw [this] at h2
    omega)
  obtain ⟨l, hl, hldvd, hlo⟩ := kc_exists_prime P (H.QS * H.q) hn0 hm
  have : P.LiesOver (kcBelow H P) := ⟨rfl⟩
  have : (H.conj • P).LiesOver (kcBelow H P) := ⟨heq⟩
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isGaloisGroup (kcBelow H P) P (H.conj • P) (H.E ≃ₐ[H.K] H.E)
  have hτ' : (τ.restrictScalars ℚ) • P = H.conj • P := hτ
  have hst : (τ.restrictScalars ℚ)⁻¹ * H.conj ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hτ', inv_smul_smul]
  have hpsi := C.decomp_typeI l hl hldvd P _ hst
  rw [map_mul, map_inv, Subgroup.mul_mem_cancel_left _ (inv_mem (kc_restrict_mem_Psi H τ)),
    kc_gal_conj] at hpsi
  exact kc_cc_not_mem hpsi
end Formalism.HC.Der
