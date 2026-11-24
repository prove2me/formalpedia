-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.normRepCount_split_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:37.743804+00:00
-- url     : https://prove2.me/submissions/88c179d4-734c-409d-82d9-7965a7380feb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_natCard_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_vecEquiv_fst
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_vecEquiv_snd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_norm_cond_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_card_dot_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open NormResidues
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M : ℕ) (hM : 1 ≤ M) (n : 𝓞 K) (hn : conjO K n = n)
    (hnP : n ∉ P) :
    (normRepCount K (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) M n : ℤ) =
      (Ideal.absNorm P : ℤ) ^ (2 * M - 1) - (Ideal.absNorm P : ℤ) ^ (M - 1) := by
  have := hP
  have := finite_quot hP
  let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Fintype.card_eq_nat_card, natCard_quot]
  have hc0 : Ideal.Quotient.mk P n ≠ 0 := fun h => hnP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have key : ∀ x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P,
      (∃ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk _ (y i) = x i) ∧
        Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (∑ i, conjO K (y i) * y i) =
          Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) n) ↔
      ∑ i, (vecEquiv hP hc M x).1 i * (vecEquiv hP hc M x).2 i = Ideal.Quotient.mk P n := by
    intro x
    constructor
    · rintro ⟨y, hy, h⟩
      rw [norm_cond_iff hP hc M n hn y] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [vecEquiv_fst, vecEquiv_snd, ← hy i, pairLift_mk]
    · intro h
      choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
      refine ⟨y, hy, ?_⟩
      rw [norm_cond_iff hP hc M n hn y, ← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [vecEquiv_fst, vecEquiv_snd, ← hy i, pairLift_mk]
  unfold normRepCount
  rw [Nat.card_congr ((Equiv.subtypeEquivRight key).trans
    (Equiv.subtypeEquiv (q := fun z : (Fin M → 𝓞 K ⧸ P) × (Fin M → 𝓞 K ⧸ P) =>
      ∑ i, z.1 i * z.2 i = Ideal.Quotient.mk P n) (vecEquiv hP hc M) fun x => Iff.rfl))]
  exact card_dot_eq (Ideal.absNorm P) hq M hM _ hc0
end Formalism.HermitianLattices.Ext.L3
