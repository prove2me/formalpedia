-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.normRepCount_pow_succ_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:54.972099+00:00
-- url     : https://prove2.me/submissions/3ec18cc6-d1c0-4960-9483-8b0daa0c5b83

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_eq_conjO_of
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_normRepCount_pow_succ_of
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_isCoprime_span_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Formalism.HermitianLattices.Ext.L3.NormLifting
namespace Formalism.HermitianLattices.Ext.L3
open NormLifting
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private lemma map_conjO_eq_conjIdeal (P : Ideal (𝓞 K)) :
    P.map (conjO K) = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal Ideal.map
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    show ((conjO K s : 𝓞 K) : K) = star ((s : 𝓞 K) : K)
    first
    | rfl
    | (symm; simp [conjO])
    | simp [conjO]
    | (unfold conjO; simp)
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (eq_conjO_of h).symm⟩
end Formalism.HermitianLattices.Ext.L3
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open NormLifting
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ (k + 1)) M n =
      Ideal.absNorm P ^ (2 * M - 1) *
        normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) M n := by
  obtain ⟨θ, t, ht, hθP⟩ := hK.2.2 P hP
  rw [eq_conjO_of ht] at hθP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  generalize hPbdef : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = Pb
  have hm : P.map (conjO K) = Pb := by rw [← hPbdef]; exact map_conjO_eq_conjIdeal P
  have hcc : (conjO K).comp (conjO K) = RingHom.id _ := RingHom.ext conjO_conjO
  have hmm : ∀ I : Ideal (𝓞 K), (I.map (conjO K)).map (conjO K) = I := fun I => by
    rw [Ideal.map_map, hcc, Ideal.map_id]
  have hPb0 : Pb ≠ ⊥ := by
    intro h
    apply hP0
    rw [← hmm P, hm, h, Ideal.map_bot]
  have hQ0 : P * Pb ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨hP0, hPb0⟩
  have hQ : (P * Pb).map (conjO K) = P * Pb := by
    rw [Ideal.map_mul, ← hm, hmm, mul_comm]
  have hcop : ∀ a, IsCoprime (Ideal.span {a}) P → IsCoprime (Ideal.span {conjO K a}) Pb := by
    intro a ha
    rw [Ideal.isCoprime_iff_sup_eq] at ha ⊢
    have h3 := congrArg (Ideal.map (conjO K)) ha
    rwa [Ideal.map_sup, Ideal.map_top, hm, Ideal.map_span, Set.image_singleton] at h3
  have h1 := isCoprime_span_of_notMem hP hθP
  have h4 := hcop _ h1
  rw [map_sub, conjO_conjO, ← Ideal.span_singleton_neg (conjO K θ - θ), neg_sub] at h4
  have hθ : IsCoprime (Ideal.span {θ - conjO K θ}) (P * Pb) := IsCoprime.mul_right h1 h4
  have h5 := isCoprime_span_of_notMem hP hnP
  have h6 := hcop _ h5
  rw [hn] at h6
  have hnQ : IsCoprime (Ideal.span {n}) (P * Pb) := IsCoprime.mul_right h5 h6
  have hnorm : Ideal.absNorm Pb = Ideal.absNorm P := by
    have hbij : Function.Bijective (conjO K) :=
      ⟨Function.LeftInverse.injective (g := conjO K) (fun x => conjO_conjO x),
        Function.RightInverse.surjective (g := conjO K) (fun x => conjO_conjO x)⟩
    let f : 𝓞 K ≃+* 𝓞 K := RingEquiv.ofBijective (conjO K) hbij
    have e := Ideal.quotientEquiv P Pb f (by rw [← hm]; rfl)
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr e.toEquiv).symm
  have hq : Ideal.absNorm (P * Pb) = Ideal.absNorm P ^ 2 := by rw [map_mul, hnorm, sq]
  have hQ' : (P * Pb).map (conjO K) = P * Pb := hQ
  exact normRepCount_pow_succ_of hQ0 hQ' θ n hθ hnQ hn (Ideal.absNorm P) hq M k hM hk
end Formalism.HermitianLattices.Ext.L3
