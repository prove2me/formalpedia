-- Prove2me | solution 1 for Formalism.HC.Der.principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:57:24.139032+00:00
-- url     : https://prove2.me/submissions/bc2bfdcf-c919-4eac-8756-11ecea721771

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
import Theorems.Thm_Formalism_HC_Der_kc_below_smul
import Theorems.Thm_Formalism_HC_Der_kc_conj_sq
import Theorems.Thm_Formalism_HC_Der_diffSupport
import Theorems.Thm_Formalism_HC_Der_kc_below_ne
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_kc_diff_smul_eq
import Theorems.Thm_Formalism_HC_Der_kc_pairing
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
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.HC.Der
theorem _root_.solution : ∃ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) ∧ 𝔟 ⊔ H.conj • 𝔟 = ⊤ ∧
    ∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ φ.Psi → σ • 𝔟 = 𝔟 := by
  have := H.galois
  obtain ⟨f, hf⟩ : ∃ f : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, f I = H.conj • I :=
    ⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) H.conj).toMulEquiv, fun _ => rfl⟩
  have hD0 : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have hfD : f (differentIdeal (𝓞 H.K) (𝓞 H.E)) = differentIdeal (𝓞 H.K) (𝓞 H.E) := by
    rw [hf]
    exact kc_diff_smul_eq H H.conj
  have hcc : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I := fun I => by
    rw [← mul_smul, kc_conj_sq, one_smul]
  let p : Ideal (𝓞 H.E) → Prop := fun P =>
    WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))
  have hp : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (differentIdeal (𝓞 H.K) (𝓞 H.E)),
      (p (f P) ↔ ¬ p P) := by
    intro P hP
    have hPp : P.IsPrime :=
      Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
    have hPd : P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hne := kc_below_ne H C P (diffSupport H C P hPp hPd)
    show WellOrderingRel (kcBelow H (f P)) (kcBelow H (H.conj • f P)) ↔
      ¬ WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))
    rw [hf, hcc]
    constructor
    · intro h1 h2
      exact asymm h1 h2
    · intro h1
      rcases trichotomous_of WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P)) with h | h | h
      · exact absurd h h1
      · exact absurd h hne
      · exact h
  obtain ⟨B, hB, -, hBtop, hinv, -⟩ := kc_pairing _ hD0 f hfD p hp
  refine ⟨B, ?_, ?_, fun σ hσ => ?_⟩
  · rw [← hf]
    exact hB
  · rw [← hf]
    exact hBtop
  · obtain ⟨g, hg⟩ : ∃ g : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, g I = σ • I :=
      ⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) σ).toMulEquiv, fun _ => rfl⟩
    rw [← hg]
    refine hinv g (by rw [hg]; exact kc_diff_smul_eq H σ) fun P _ => ?_
    have hn : H.gal (H.conj * σ * H.conj⁻¹) ∈ φ.Psi := by
      have hσ' : φ.chD (H.gal σ) = 1 := hσ
      show φ.chD (H.gal (H.conj * σ * H.conj⁻¹)) = 1
      simp only [map_mul, map_inv, hσ', mul_one, mul_inv_cancel]
    have e1 : (H.conj * σ * H.conj⁻¹) • H.conj • P = H.conj • σ • P := by
      rw [← mul_smul, inv_mul_cancel_right, mul_smul]
    show WellOrderingRel (kcBelow H (g P)) (kcBelow H (H.conj • g P)) ↔
      WellOrderingRel (kcBelow H P) (kcBelow H (H.conj • P))
    rw [hg, kc_below_smul H σ hσ P, ← e1, kc_below_smul H _ hn]
end Formalism.HC.Der
