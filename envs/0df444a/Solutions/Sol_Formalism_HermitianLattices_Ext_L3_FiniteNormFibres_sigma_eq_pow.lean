-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.sigma_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:06.328802+00:00
-- url     : https://prove2.me/submissions/d4c8e99d-6f18-4555-92a6-5a3e947770d3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteNormFibres
namespace Formalism.HermitianLattices.Ext.L3.FiniteNormFibres
theorem _root_.solution {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2) :
    ∀ x, σ x = x ^ q := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k p
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  have hpow : ∀ i : ℕ, ∀ x : k,
      ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ i) x = x ^ (p ^ i) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ, AlgEquiv.mul_apply, ih]
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]
      rw [← pow_mul, ← pow_succ']
  let σ' : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := σ) (fun c =>
    DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) k))
      (algebraMap (ZMod p) k)) c)
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 σ'
  have hj' : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ (j : ℕ) = σ' := hj
  have hσj : ∀ x, σ x = x ^ (p ^ (j : ℕ)) := fun x => by rw [← hpow, hj']; rfl
  have hN : Fintype.card k = p ^ Module.finrank (ZMod p) k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := k), ZMod.card]
  have hfrN : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ Module.finrank (ZMod p) k = 1 :=
    AlgEquiv.ext fun x => by rw [hpow, AlgEquiv.one_apply, ← hN, FiniteField.pow_card]
  have hσ2 : σ' ^ 2 = 1 := AlgEquiv.ext fun x => by
    rw [pow_two, AlgEquiv.mul_apply]
    exact hσ x
  rw [← hj', ← pow_mul] at hσ2
  have hN0 : 0 < Module.finrank (ZMod p) k := Fin.pos j
  have hr : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^
      ((j : ℕ) * 2 % Module.finrank (ZMod p) k) = 1 := by
    have h1 := Nat.mod_add_div ((j : ℕ) * 2) (Module.finrank (ZMod p) k)
    rw [← h1, pow_add, pow_mul, hfrN, one_pow, mul_one] at hσ2
    exact hσ2
  have hr0 : (j : ℕ) * 2 % Module.finrank (ZMod p) k = 0 := by
    have h1 := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).1
      (a₁ := ⟨(j : ℕ) * 2 % Module.finrank (ZMod p) k, Nat.mod_lt _ hN0⟩) (a₂ := ⟨0, hN0⟩)
      (by simp only [pow_zero]; exact hr)
    exact congrArg Fin.val h1
  have hj0 : (j : ℕ) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hne
    apply hx
    rw [hσj, h0, pow_zero, pow_one]
  have hjlt := j.isLt
  have ht := Nat.mod_add_div ((j : ℕ) * 2) (Module.finrank (ZMod p) k)
  rw [hr0, zero_add] at ht
  obtain ⟨t, ht2⟩ : ∃ t, Module.finrank (ZMod p) k * t = (j : ℕ) * 2 := ⟨_, ht⟩
  have h2j : (j : ℕ) * 2 = Module.finrank (ZMod p) k := by
    rcases t with _ | _ | t
    · simp at ht2
      omega
    · simp at ht2
      omega
    · exfalso
      nlinarith
  have hqj : q = p ^ (j : ℕ) := by
    have h1 : q ^ 2 = (p ^ (j : ℕ)) ^ 2 := by rw [← hq, hN, ← pow_mul, h2j]
    exact Nat.pow_left_injective two_ne_zero h1
  intro x
  rw [hσj, hqj]
end Formalism.HermitianLattices.Ext.L3.FiniteNormFibres
