-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.stab_frob_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:58:58.758286+00:00
-- url     : https://prove2.me/submissions/18f09a5e-86d5-4bfb-8f49-2fc9a8768ee1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_frob_pow_mk
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Decomp
namespace Formalism.FrobeniusOrbits.Decomp
theorem _root_.solution {M : Type} [Field M] [NumberField M] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (F σ : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (hσ : σ ∈ MulAction.stabilizer Gal(M/ℚ) Q) :
    ∃ k : ℕ, ∀ x : 𝓞 M, σ • x - (F ^ k) • x ∈ Q := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hund : span {(p : ℤ)} = Q.under ℤ := Ideal.LiesOver.over
  have hQ0 : Q ≠ ⊥ := by
    intro hQ
    have h1 : (p : ℤ) ∈ Q.under ℤ := by
      rw [← hund]
      exact Ideal.mem_span_singleton_self _
    have h2 := Ideal.mem_comap.mp h1
    rw [hQ, Ideal.mem_bot] at h2
    exact hp.ne_zero (by simpa using h2)
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  letI : Field (𝓞 M ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (𝓞 M ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  haveI : CharP (𝓞 M ⧸ Q) p := by
    refine ⟨fun n => ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk Q) n, Ideal.Quotient.eq_zero_iff_mem]
    have e1 : (n : 𝓞 M) ∈ Q ↔ (n : ℤ) ∈ Q.under ℤ :=
      ⟨fun h => Ideal.mem_comap.mpr (by rwa [map_natCast]),
        fun h => by simpa using Ideal.mem_comap.mp h⟩
    rw [e1, ← hund, Ideal.mem_span_singleton]
    norm_cast
  letI : Algebra (ZMod p) (𝓞 M ⧸ Q) := ZMod.algebra _ p
  have hσQ : Q ≤ Q.comap (MulSemiringAction.toRingHom _ (𝓞 M) σ) := by
    intro y hy
    rw [Ideal.mem_comap, MulSemiringAction.toRingHom_apply]
    have hσ' : σ • Q = Q := MulAction.mem_stabilizer_iff.mp hσ
    rw [← hσ', Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
    exact hy
  let sb : (𝓞 M ⧸ Q) →+* (𝓞 M ⧸ Q) :=
    Ideal.quotientMap Q (MulSemiringAction.toRingHom _ (𝓞 M) σ) hσQ
  let sa : (𝓞 M ⧸ Q) →ₐ[ZMod p] (𝓞 M ⧸ Q) :=
    { sb with
      commutes' := fun c => by
        change sb (algebraMap (ZMod p) _ c) = algebraMap (ZMod p) _ c
        rw [← ZMod.natCast_zmod_val c, map_natCast, map_natCast] }
  obtain ⟨⟨n, hlt⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (𝓞 M ⧸ Q)).2 sa
  have hn' : FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ n = sa := hn
  have key : ∀ m : ℕ, ∀ y : 𝓞 M ⧸ Q,
      (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ m) y = y ^ (p ^ m) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ' (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q)) m, AlgHom.mul_apply, ih,
        FiniteField.frobeniusAlgHom_apply, ZMod.card, ← pow_mul, ← pow_succ p m]
  refine ⟨n, fun x => ?_⟩
  rw [← Ideal.Quotient.eq]
  have h1 : sa (Ideal.Quotient.mk Q x) = Ideal.Quotient.mk Q (σ • x) := rfl
  rw [← h1, ← hn', key, frob_pow_mk p Q F hF n x]
end Formalism.FrobeniusOrbits.Decomp
