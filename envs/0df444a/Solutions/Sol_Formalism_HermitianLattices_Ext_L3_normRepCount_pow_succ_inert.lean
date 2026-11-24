-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.normRepCount_pow_succ_inert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:54.886002+00:00
-- url     : https://prove2.me/submissions/b8f00010-fbd6-47f1-aadd-c2a133b74f91

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_eq_conjO_of
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_normRepCount_pow_succ_of
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_isCoprime_span_of_notMem
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
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) (q : ℕ)
    (hq : Ideal.absNorm P = q ^ 2) :
    normRepCount K (P ^ (k + 1)) M n = q ^ (2 * M - 1) * normRepCount K (P ^ k) M n := by
  obtain ⟨θ, t, ht, hθP⟩ := hK.2.2 P hP
  rw [eq_conjO_of ht] at hθP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hmap : P.map (conjO K) = P := by rw [map_conjO_eq_conjIdeal]; exact hc
  exact normRepCount_pow_succ_of hP0 hmap θ n (isCoprime_span_of_notMem hP hθP)
    (isCoprime_span_of_notMem hP hnP) hn q hq M k hM hk
end Formalism.HermitianLattices.Ext.L3
