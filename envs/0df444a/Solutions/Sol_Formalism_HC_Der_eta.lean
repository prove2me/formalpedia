-- Prove2me | solution 1 for Formalism.HC.Der.eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:59.121315+00:00
-- url     : https://prove2.me/submissions/928e8d18-8e01-439e-a3a3-01ab7ffdc29e

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Theorems.Thm_Formalism_HC_Der_kc_gal_conj
import Theorems.Thm_Formalism_HC_Der_kc_ne_bot
import Theorems.Thm_Formalism_HC_Der_kc_conj_eq
import Theorems.Thm_Formalism_HC_Der_kc_unr
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_eq_inertia_mul
import Theorems.Thm_Formalism_FrobeniusOrbits_Eta_ncard_eq_two_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Eta_split_or_inert
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_frob
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
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
theorem _root_.solution : (∀ 𝔭 : Ideal (𝓞 H.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (primesOver 𝔭 (𝓞 H.E)).ncard = 2 ∨ ((primesOver 𝔭 (𝓞 H.E)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 H.E) = 2)) ∧
    (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
        (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ φ.cc ∈ Subgroup.zpowers (H.gal σ))) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1) := by
  have := C.cm
  have hunr := kc_unr H C
  have hsm : ∀ P : Ideal (𝓞 H.E), IsCMField.complexConj H.E • P = H.conj • P := fun P => by
    rw [← kc_conj_eq H C]
    rfl
  have hetaiff : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ≠ ⊥ →
      (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ↔ H.conj • P ≠ P) := by
    intro P _ hP0
    have hk := Eta.ncard_eq_two_iff H.E hunr P hP0
    rw [hsm] at hk
    unfold HostRaw.etaF
    change (if (primesOver (P.under (𝓞 H.F)) (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 ↔ _
    rw [← hk]
    split_ifs with h2
    · exact iff_of_true rfl h2
    · exact iff_of_false (by decide) h2
  refine ⟨fun 𝔭 hp h0 => ?_, ?_, ?_⟩
  · have := hp
    exact Eta.split_or_inert H.E hunr 𝔭 h0
  · intro p hpf hN P _ _ σ hσ
    have hP0 := kc_ne_bot p hpf.out P
    have hm1 : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ H.conj • P = P := by
      have h1 := hetaiff P hP0
      have hval : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ∨
          H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 := by
        unfold HostRaw.etaF; split_ifs <;> simp
      constructor
      · intro hm
        by_contra hc
        rw [h1.mpr hc] at hm
        exact absurd hm (by decide)
      · intro hfix
        rcases hval with hv | hv
        · exact absurd hfix (h1.mp hv)
        · exact hv
    rw [hm1]
    constructor
    · intro hfix
      have hst : H.conj ∈ MulAction.stabilizer _ P := hfix
      obtain ⟨k, ρ, hρ, hρeq⟩ := Decomp.stab_eq_inertia_mul p P σ H.conj hσ hst
      rw [((C.frob p hN P).2.2.2 ρ).mp hρ, one_mul] at hρeq
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [zpow_natCast, ← map_pow, ← hρeq, kc_gal_conj]⟩
    · intro hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hσc : σ ^ k = H.conj := H.gal.injective (by rw [map_zpow, hk, kc_gal_conj])
      rw [← hσc]
      exact Subgroup.zpow_mem _ hσ.mem_stabilizer k
  · intro p hpf hN P _ _
    exact (hetaiff P (kc_ne_bot p hpf.out P)).mpr (C.decompConj p hpf.out hN P)
end Formalism.HC.Der
