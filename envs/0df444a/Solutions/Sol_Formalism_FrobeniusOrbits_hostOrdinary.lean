-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostOrdinary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:08:26.898817+00:00
-- url     : https://prove2.me/submissions/aeae5926-a583-4a68-b6fb-c1342b0bc595

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrdUnimod
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecomp
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostSplitK_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply


section
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace OrdUnimod
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end OrdUnimod
open OrdUnimod
private theorem mem_stabilizer_of_isArithFrobAt {L : Type} [Field L] [NumberField L] {ζ a b : L}
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime]
    (h : IsArithFrobAt ℤ σ P) :
    σ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P := by
  have hc := h.comap_eq
  have key : ∀ y : 𝓞 (hostE ζ a b), y ∈ P ↔ σ • y ∈ P := by
    intro y
    have := congrArg (fun I : Ideal (𝓞 (hostE ζ a b)) => y ∈ I) hc
    simp only [Ideal.mem_comap] at this
    rw [← this]
    first
    | rfl
    | exact Iff.rfl
    | simp
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hx
    have := (key _).mp hx
    rwa [smul_inv_smul] at this
  · intro hx
    exact (key _).mpr (by rw [smul_inv_smul]; exact hx)
private theorem galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
    (hodd : HypOdd q d) (hL : IsLayer (e + 2) q d ζ a b)
    (p : ℕ) [hpF : Fact p.Prime] (hp2 : p ≠ 2) (hpd : p ≠ d)
    (P : Ideal (𝓞 (hostE ζ a b))) [hPp : P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (hj : jacobiSym (-(d : ℤ)) p = 1)
    (τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hτ : τ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P) :
    (galE e ζ a b τ).1.2 = 1 := by
  have hodd' : q.Prime ∧ d.Prime ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2 := hodd
  have hL' : IsPrimitiveRoot ζ (2 ^ (e + 2)) ∧ a ^ 2 = -(q : L) ∧ b ^ 2 = -(d : L) ∧
      IntermediateField.adjoin ℚ {ζ, a, b} = ⊤ := hL
  have hp : p.Prime := hpF.out
  have hspec := (hostGalSpec e q d hodd L ζ a b hL τ).2.1
  by_contra hs
  have hs' : (galE e ζ a b τ).1.2 = -1 := (Int.units_eq_one_or _).resolve_left hs
  have hτb : τ (bE ζ a b) = -(bE ζ a b) := by
    apply Subtype.ext
    rw [hspec, hs']
    first
    | simp [bE]
    | (simp; rfl)
  have hb2 : (bE ζ a b) ^ 2 = algebraMap ℤ (hostE ζ a b) (-(d : ℤ)) := by
    apply Subtype.ext
    first
    | simp [bE, hL'.2.2.1]
    | (simp [bE]; exact hL'.2.2.1)
  have hbI : IsIntegral ℤ (bE ζ a b) := by
    have h := isIntegral_algebraMap (R := ℤ) (A := hostE ζ a b) (x := -(d : ℤ))
    rw [← hb2] at h
    exact IsIntegral.of_pow two_pos h
  obtain ⟨β, hβ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 (hostE ζ a b))).mp hbI
  have hinj : Function.Injective (algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b)) := by
    first
    | exact IsIntegralClosure.algebraMap_injective (𝓞 (hostE ζ a b)) ℤ (hostE ζ a b)
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact IsFractionRing.injective _ _
  have hcomm : ∀ z : 𝓞 (hostE ζ a b),
      algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) (τ • z) =
        τ (algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) z) := by
    intro z
    first
    | rfl
    | simp
    | exact NumberField.RingOfIntegers.coe_smul _ _
  have hβ2 : β ^ 2 = -(d : 𝓞 (hostE ζ a b)) := by
    apply hinj
    rw [map_pow, hβ, hb2]
    simp
  have hZ : ∀ x : ℤ, (x : 𝓞 (hostE ζ a b)) ∈ P ↔ (p : ℤ) ∣ x := by
    intro x
    rw [← eq_intCast (algebraMap ℤ (𝓞 (hostE ζ a b))) x, ← Ideal.mem_span_singleton]
    first
    | exact (Ideal.mem_of_liesOver P (span {(p : ℤ)}) x).symm
    | (rw [Ideal.over_def P (span {(p : ℤ)})]; rfl)
    | (rw [Ideal.LiesOver.over (P := P) (p := span {(p : ℤ)})]; rfl)
    | (rw [Ideal.over_def P (span {(p : ℤ)})]; simp [Ideal.under])
  have hsq : IsSquare (((-(d : ℤ)) : ℤ) : ZMod p) := by
    have hl : legendreSym p (-(d : ℤ)) = 1 := by
      first
      | (rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj)
      | (rw [← jacobiSym.legendreSym.to_jacobiSym] at hj; exact hj)
      | (simp [jacobiSym, Nat.primeFactorsList_prime hp] at hj; exact hj)
    have h0 : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      have := (legendreSym.eq_zero_iff p (-(d : ℤ))).mpr h0
      rw [hl] at this
      exact one_ne_zero this
    exact (legendreSym.eq_one_iff p h0).mp hl
  obtain ⟨c, hc⟩ := hsq
  obtain ⟨r, hr⟩ : ∃ r : ℤ, (r : ZMod p) = c := ⟨c.val, by
    first
    | simp
    | exact_mod_cast ZMod.natCast_zmod_val c⟩
  have hdiv : (p : ℤ) ∣ r * r + d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hr, ← hc]
    push_cast
    ring
  have hstab : τ • P = P := MulAction.mem_stabilizer_iff.mp hτ
  have key : ∀ s : ℤ, β - (s : 𝓞 (hostE ζ a b)) ∈ P → False := by
    intro s hs
    have h1 : τ • (β - (s : 𝓞 (hostE ζ a b))) ∈ P := by
      have hm : τ • (β - (s : 𝓞 (hostE ζ a b))) ∈ τ • P := by
        first
        | exact Ideal.smul_mem_pointwise_smul τ _ P hs
        | exact Submodule.smul_mem_pointwise_smul _ τ P hs
        | exact Set.smul_mem_smul_set hs
      rwa [hstab] at hm
    have h2 : τ • (β - (s : 𝓞 (hostE ζ a b))) = -β - (s : 𝓞 (hostE ζ a b)) := by
      apply hinj
      rw [hcomm]
      simp [hβ, hτb]
    rw [h2] at h1
    have e3 : ((4 * (d : ℤ) : ℤ) : 𝓞 (hostE ζ a b)) =
        -(((β - s) - (-β - s)) * ((β - s) - (-β - s))) := by
      push_cast
      linear_combination 4 * hβ2
    have h3 : ((4 * (d : ℤ) : ℤ) : 𝓞 (hostE ζ a b)) ∈ P := by
      rw [e3]
      exact neg_mem (Ideal.mul_mem_left _ _ (sub_mem hs h1))
    have h4 : p ∣ 4 * d := by
      have := (hZ _).mp h3
      exact_mod_cast this
    rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h5)))
    · exact hpd ((Nat.prime_dvd_prime_iff_eq hp hodd'.2.1).mp h5)
  have hm : (β - (r : 𝓞 (hostE ζ a b))) * (β - ((-r : ℤ) : 𝓞 (hostE ζ a b))) ∈ P := by
    have e4 : (β - (r : 𝓞 (hostE ζ a b))) * (β - ((-r : ℤ) : 𝓞 (hostE ζ a b))) =
        (((-(r * r + d)) : ℤ) : 𝓞 (hostE ζ a b)) := by
      push_cast
      linear_combination hβ2
    rw [e4, hZ]
    exact dvd_neg.mpr hdiv
  rcases hPp.mem_or_mem hm with h | h
  · exact key r h
  · exact key (-r) h
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open OrdUnimod
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostOrdinary := by
  intro e q d hH L _ _ ζ a b hL p _ P _ _
  have hH' : q.Prime ∧ d.Prime ∧ q % 8 = 3 ∧ d % 16 = 7 ∧ jacobiSym (-(d : ℤ)) q = 1 := hH
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH'
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hodd : HypOdd q d := show q.Prime ∧ d.Prime ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2 from
    ⟨hq, hd, by omega, hq2, hd2⟩
  have hG := hostGalois e q d hodd L ζ a b hL
  have hmul := hG.2.2.1
  have hbij := hG.2.2.2
  have hg1 : galE e ζ a b 1 = 1 := by
    first
    | exact map_one (MonoidHom.mk' (galE e ζ a b) hmul)
    | (have h11 := hmul 1 1; rw [one_mul] at h11; exact (mul_eq_left.mp h11.symm))
  have hPsi : ∀ g : GG e, g ∈ Psi e ↔ g.1.2 = 1 := by
    intro g
    first
    | exact Iff.rfl
    | (rw [Psi, MonoidHom.mem_ker]; rfl)
    | simp [Psi, chD]
  have hS := hostSplitK_of (hostFrob_of hostGalois hostGalSpec) e q d hH L ζ a b hL
  have hF := hostFrob_of hostGalois hostGalSpec e q d hodd L ζ a b hL
  have hcq : Nat.Coprime q (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  have hcd : Nat.Coprime d (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hd Nat.prime_two).mpr hd2)
  have hD := hostDecomp e q d hH L ζ a b hL (ZMod.unitOfCoprime q hcq) (ZMod.unitOfCoprime d hcd)
    (ZMod.coe_unitOfCoprime _ _) (ZMod.coe_unitOfCoprime _ _)
  have key : (∀ σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, τ ∈ MulAction.stabilizer _ P →
      (galE e ζ a b (σ * τ) ∈ Psi e ↔ galE e ζ a b σ ∈ Psi e)) ↔
      ∀ τ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P, galE e ζ a b τ ∈ Psi e := by
    constructor
    · intro h τ hτ
      have h1 := h 1 τ hτ
      rw [one_mul] at h1
      exact h1.mpr (by rw [hg1]; exact (Psi e).one_mem)
    · intro h σ τ hτ
      rw [hmul]
      exact Subgroup.mul_mem_cancel_right _ (h τ hτ)
  rw [key]
  by_cases hp2 : p = 2
  · subst hp2
    haveI : P.LiesOver (span {(2 : ℤ)}) := by
      simpa using (inferInstance : P.LiesOver (span {((2 : ℕ) : ℤ)}))
    exact iff_of_true (fun τ hτ => ((hD τ).1 P).mp hτ) ((hS.1 2 Nat.prime_two).mpr (Or.inl rfl))
  by_cases hpq : p = q
  · subst hpq
    refine iff_of_true (fun τ hτ => ?_) hS.2.2.1
    rw [hPsi]
    exact (((hD τ).2.1 P).mp hτ).1
  by_cases hpd : p = d
  · subst hpd
    refine iff_of_false (fun h => ?_) (by rw [hS.2.1]; decide)
    obtain ⟨σ0, hσ0⟩ := hbij.2 (((-1 : ℤˣ), (-1 : ℤˣ)), hcl e (ZMod.unitOfCoprime p hcd))
    have hst : σ0 ∈ MulAction.stabilizer _ P :=
      ((hD σ0).2.2 P).mpr ⟨1, by rw [hσ0, pow_one], by rw [hσ0, pow_one]⟩
    have h1 := (hPsi _).mp (h σ0 hst)
    rw [hσ0] at h1
    exact absurd (congrArg Units.val h1) (by norm_num)
  obtain ⟨φ, hφ⟩ := (hF p hp2 hpq hpd P).1
  rw [← hS.2.2.2 p hp2 hpq hpd P φ hφ]
  constructor
  · intro h
    exact h φ (mem_stabilizer_of_isArithFrobAt φ P hφ)
  · intro hφΨ τ hτ
    rw [hPsi]
    have hj : jacobiSym (-(d : ℤ)) p = 1 := by
      have h2 := (hS.2.2.2 p hp2 hpq hpd P φ hφ).mp hφΨ
      rcases (hS.1 p (Fact.out)).mp h2 with h | ⟨-, h⟩
      · exact absurd h hp2
      · exact h
    exact galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one hodd hL p hp2 hpd P hj τ hτ
end Formalism.FrobeniusOrbits
