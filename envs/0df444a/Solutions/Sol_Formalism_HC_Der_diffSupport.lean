-- Prove2me | solution 1 for Formalism.HC.Der.diffSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:50:10.346279+00:00
-- url     : https://prove2.me/submissions/0c6c93cf-61aa-44e4-aa50-a045229d553e

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
import Theorems.Thm_Formalism_HC_Der_kc_exists_prime
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_kc_iod_not_mem
import Theorems.Thm_Formalism_HC_Der_kc_not_dvd_different
import Theorems.Thm_Formalism_HC_Der_kc_restrict_mem_Psi
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
theorem _root_.solution : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) →
    ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P := by
  intro P hP hdvd
  have := H.galois
  by_contra hnot
  refine kc_not_dvd_different H.K H.E P ?_ hdvd
  intro hbot σ hσ
  have hn0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  obtain ⟨l, hl, -, hlo⟩ := kc_exists_prime P (Ideal.absNorm P) hn0 (Ideal.absNorm_mem P)
  have : Fact l.Prime := ⟨hl⟩
  have hlP : (l : 𝓞 H.E) ∈ P := by
    have h1 : (l : ℤ) ∈ P.under ℤ := by
      rw [← hlo.over]
      exact Ideal.mem_span_singleton_self _
    simpa using h1
  have hlq : ¬ l ∣ H.QS * H.q := by
    rintro ⟨m, hm⟩
    apply hnot
    rw [hm, Nat.cast_mul]
    exact P.mul_mem_right _ hlP
  obtain ⟨u, hu, hgal⟩ := (C.inertia l P (σ.restrictScalars ℚ)).mp fun x => hσ x
  have hmod : (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] :=
    Nat.ModEq.of_dvd (Nat.dvd_ordCompl_of_dvd_not_dvd (Dvd.intro _ rfl) hlq) hu
  rcases H.art_d u hmod with h1 | h1
  · have h2 : σ.restrictScalars ℚ = 1 := H.gal.injective (by rw [hgal, h1, map_one])
    ext x
    exact congrArg (fun τ : H.E ≃ₐ[ℚ] H.E => τ x) h2
  · exfalso
    have hpsi := kc_restrict_mem_Psi H σ
    rw [hgal, h1] at hpsi
    exact kc_iod_not_mem hpsi
end Formalism.HC.Der
