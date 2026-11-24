-- Prove2me | solution 1 for Formalism.HC.Der.ordinary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:28:16.909295+00:00
-- url     : https://prove2.me/submissions/9cf0c5b5-3b34-4f97-bd07-4ed649a93782

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Theorems.Thm_Formalism_HC_Der_kc_iod_not_mem
import Theorems.Thm_Formalism_HC_Der_kc_two_dvd
import Theorems.Thm_Formalism_HC_Der_kc_stab_of_inertia
import Theorems.Thm_Formalism_HC_Der_splitK
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_eq_inertia_mul
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_frob
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_splitK
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Frame_mem_Psi_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



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
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔
      (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 := by
  intro p hpf P _ _
  have hp : p.Prime := hpf.out
  have hred : (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P →
      (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔
      ∀ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → H.gal τ ∈ φ.Psi := by
    constructor
    · intro h τ hτ
      have := h 1 τ hτ
      rw [one_mul, map_one] at this
      exact this.mpr (one_mem _)
    · intro h σ τ hτ
      rw [map_mul]
      exact Subgroup.mul_mem_cancel_right _ (h τ hτ)
  rw [hred, splitK H p hp]
  by_cases h1 : p ∣ H.QS * H.q
  · refine iff_of_true (fun τ hτ => C.decomp_typeI p hp h1 P τ hτ) ?_
    by_cases h2 : p = 2
    · exact Or.inl h2
    · refine Or.inr ⟨h2, ?_⟩
      rcases hp.dvd_mul.mp h1 with h3 | h3
      · exact H.QS_split p hp h2 h3
      · rw [(Nat.prime_dvd_prime_iff_eq hp H.hyp.1).mp h3]
        exact H.hyp.2.2.2.2
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h1 ((kc_two_dvd H).mul_right _)
  by_cases hpd : p = H.d
  · subst hpd
    refine iff_of_false (fun h => ?_) ?_
    · obtain ⟨σ, hσ⟩ := H.gal.surjective φ.iod
      have h3 := h σ (kc_stab_of_inertia σ P ((C.inertia_d P σ).mpr (Or.inr hσ)))
      rw [hσ] at h3
      exact kc_iod_not_mem h3
    · rintro (h | ⟨-, h⟩)
      · exact hp2 h
      · have : NeZero H.d := ⟨hp.ne_zero⟩
        have h0 : jacobiSym (-(H.d : ℤ)) H.d = 0 :=
          jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa using hp.ne_one)
        omega
  · have hN : ¬ p ∣ H.condN := fun h => by
      rcases hp.dvd_mul.mp h with h3 | h3
      · exact h1 h3
      · exact hpd ((Nat.prime_dvd_prime_iff_eq hp H.hyp.2.1).mp h3)
    obtain ⟨⟨F, hF⟩, -, f3, f4⟩ := C.frob p hN P
    have hj := (f3 F hF).2.1
    have hFP : H.gal F ∈ φ.Psi ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)) := by
      rw [Frame.mem_Psi_iff, ← hj, or_iff_right hp2, and_iff_right hp2]
      exact (Units.val_eq_one).symm
    rw [← hFP]
    constructor
    · intro h
      exact h F hF.mem_stabilizer
    · intro hFm τ hτ
      obtain ⟨k, ρ, hρ, rfl⟩ := Decomp.stab_eq_inertia_mul p P F τ hF hτ
      rw [(f4 ρ).mp hρ, one_mul, map_pow]
      exact Subgroup.pow_mem _ hFm k
end Formalism.HC.Der
