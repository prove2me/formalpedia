-- Prove2me | solution 1 for Formalism.HC.Der.frob_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:45.891712+00:00
-- url     : https://prove2.me/submissions/2c79c9bd-0cab-4451-8e08-9da0f65940b2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_HC_Der_tauN_frob
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_gal_eq_art_iff
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


section
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
section Cyc
variable (N : ℕ) [NeZero N]
variable (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime] [Q.LiesOver (span {(l : ℤ)})]
end Cyc
variable {φ : Frame} (H : HostRaw φ)
private lemma lift_lemma' (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ Q : Ideal (𝓞 (Cond.Cyc H.condN)), Q.IsPrime ∧ Q.LiesOver (span {(l : ℤ)}) ∧
      Q.comap (RingOfIntegers.mapRingHom (emb H).toRingHom) = P := by
  classical
  letI : Algebra (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) := (RingOfIntegers.mapRingHom (emb H).toRingHom).toAlgebra
  haveI : Algebra.IsIntegral (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) :=
    ⟨fun y => (RingOfIntegers.isIntegral y).tower_top⟩
  have hinj : Function.Injective (RingOfIntegers.mapRingHom (emb H).toRingHom) := by
    intro x y hxy
    apply RingOfIntegers.ext
    have h1 := congrArg (fun z : 𝓞 (Cond.Cyc H.condN) => (z : Cond.Cyc H.condN)) hxy
    exact (emb H).toRingHom.injective h1
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 (Cond.Cyc H.condN))) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have hx0 : x = 0 := hinj (hx.trans (map_zero _).symm)
    rw [hx0]
    exact P.zero_mem)
  refine ⟨Q, hQp, ⟨?_⟩, hQ⟩
  have hP : span {(l : ℤ)} = P.under ℤ := Ideal.LiesOver.over
  rw [hP, ← hQ]
  show Ideal.comap (algebraMap ℤ (𝓞 H.E)) (Ideal.comap (algebraMap (𝓞 H.E) (𝓞 (Cond.Cyc H.condN))) Q) =
    Ideal.comap (algebraMap ℤ (𝓞 (Cond.Cyc H.condN))) Q
  rw [Ideal.comap_comap]
  congr 1
  exact RingHom.ext_int _ _
end Formalism.HC.Der
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN])
    (h : H.gal σ = H.art u) : IsArithFrobAt ℤ σ P := by
  obtain ⟨Q, hQp, hQl, hQ⟩ := lift_lemma' H l P
  haveI := hQp
  haveI := hQl
  have hτ := tauN_frob H.condN l Q u hu
  have hact : ∀ x : 𝓞 H.E, RingOfIntegers.mapRingHom (emb H).toRingHom (σ • x) =
      tauN H.condN u • RingOfIntegers.mapRingHom (emb H).toRingHom x := by
    intro x
    apply RingOfIntegers.ext
    exact (gal_eq_art_iff H σ u).1 h x
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = Nat.card (ℤ ⧸ Q.under ℤ) := by
    rw [← Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)}), ← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)})]
  unfold IsArithFrobAt at hτ ⊢
  intro x
  rw [hcard, ← hQ, Ideal.mem_comap]
  simp only [MulSemiringAction.toAlgHom_apply] at hτ ⊢
  rw [map_sub, map_pow, hact]
  exact hτ _
end Formalism.HC.Der
