-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.card_pLen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:35.260493+00:00
-- url     : https://prove2.me/submissions/f9b273a9-6942-4fd3-aba0-b9afa4afeba0

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_pLen_add
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_pLen_self
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_pLen_simple_ne
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_kill_of_equiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_pLen_simple_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution : ∀ (n : ℕ) (A B : Submodule R W), B ≤ A →
    B.toAddSubgroup.relIndex A.toAddSubgroup = n → n ≠ 0 →
    ∃ k : {p : Ideal R // p.IsMaximal} →₀ ℕ,
      (∀ w : {p : Ideal R // p.IsMaximal}, (haveI := w.2.isPrime; pLen w.1 A B) = (k w : ℕ∞)) ∧
      B.toAddSubgroup.relIndex A.toAddSubgroup = k.prod fun w j => Nat.card (R ⧸ w.1) ^ j := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B hBA hn hn0
  by_cases hEq : B = A
  · subst hEq
    refine ⟨0, fun w => ?_, ?_⟩
    · have := w.2.isPrime
      rw [pLen_self]; simp
    · rw [Finsupp.prod_zero_index, AddSubgroup.relIndex_self]
  · set B' := B.comap A.subtype with hB'
    have hcard : Nat.card (A ⧸ B') ≠ 0 := by rw [← hn] at hn0; exact hn0
    have hfin : Finite (A ⧸ B') := Nat.finite_of_card_ne_zero hcard
    have hnt : Nontrivial (A ⧸ B') := by
      rw [Submodule.Quotient.nontrivial_iff]
      intro htop
      exact hEq (le_antisymm hBA (Submodule.comap_subtype_eq_top.1 htop))
    rcases eq_top_or_exists_le_coatom (⊥ : Submodule R (A ⧸ B')) with h | ⟨Q1, hQ1, -⟩
    · exact absurd h bot_ne_top
    · have hsimple : IsSimpleModule R ((A ⧸ B') ⧸ Q1) := isSimpleModule_iff_isCoatom.2 hQ1
      obtain ⟨m0, hm0, ⟨e0⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      set C' : Submodule R A := Q1.comap B'.mkQ with hC'
      set C : Submodule R W := C'.map A.subtype with hC
      have hCA : C ≤ A := Submodule.map_subtype_le A C'
      have hCc : C.comap A.subtype = C' :=
        Submodule.comap_map_eq_of_injective A.injective_subtype C'
      have hBC : B ≤ C := by
        intro x hx
        refine ⟨⟨x, hBA hx⟩, ?_, rfl⟩
        show B'.mkQ ⟨x, hBA hx⟩ ∈ Q1
        have : B'.mkQ ⟨x, hBA hx⟩ = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hx
        rw [this]; exact Q1.zero_mem
      have hker : LinearMap.ker (Q1.mkQ ∘ₗ B'.mkQ) = C.comap A.subtype := by
        rw [LinearMap.ker_comp, Submodule.ker_mkQ, hCc]
      have hsurj : Function.Surjective (Q1.mkQ ∘ₗ B'.mkQ) :=
        Q1.mkQ_surjective.comp B'.mkQ_surjective
      have e : (A ⧸ C.comap A.subtype) ≃ₗ[R] (R ⧸ m0) :=
        ((Submodule.quotEquivOfEq _ _ hker.symm).trans
          ((Q1.mkQ ∘ₗ B'.mkQ).quotKerEquivOfSurjective hsurj)).trans e0
      have hmul := AddSubgroup.relIndex_mul_relIndex B.toAddSubgroup C.toAddSubgroup
        A.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 hBC)
        ((Submodule.toAddSubgroup_le _ _).2 hCA)
      have hCAcard : C.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ m0) := by
        change Nat.card (A ⧸ C.comap A.subtype) = _
        exact Nat.card_congr e.toEquiv
      have hne : B.toAddSubgroup.relIndex C.toAddSubgroup ≠ 0 := by
        intro h0; rw [h0, zero_mul, hn] at hmul; exact hn0 hmul.symm
      have hne2 : Nat.card (R ⧸ m0) ≠ 0 := by
        intro h0; rw [hCAcard, h0, mul_zero, hn] at hmul; exact hn0 hmul.symm
      have h1 : 1 < Nat.card (R ⧸ m0) := by
        have : Finite (R ⧸ m0) := Nat.finite_of_card_ne_zero hne2
        have : Nontrivial (R ⧸ m0) := Ideal.Quotient.nontrivial_iff.2 hm0.ne_top
        exact Finite.one_lt_card
      have hlt : B.toAddSubgroup.relIndex C.toAddSubgroup < n := by
        rw [← hn, ← hmul, hCAcard]
        have := Nat.pos_of_ne_zero hne
        nlinarith
      obtain ⟨k1, hk1, hk1c⟩ := ih _ hlt C B hBC rfl hne
      refine ⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩
      · have := w.2.isPrime
        have := w.2
        rw [pLen_add w.1 hBC hCA, hk1 w, Finsupp.add_apply, Finsupp.single_apply]
        by_cases hw : (⟨m0, hm0⟩ : {p : Ideal R // p.IsMaximal}) = w
        · subst hw
          rw [if_pos rfl, pLen_simple_self m0 e]; simp
        · rw [if_neg hw, pLen_simple_ne w.1 m0 (fun h => hw (Subtype.ext h.symm))
            (kill_of_equiv m0 e)]; simp
      · have hz : ∀ w : {p : Ideal R // p.IsMaximal}, Nat.card (R ⧸ w.1) ^ 0 = 1 :=
          fun _ => pow_zero _
        have ha : ∀ (w : {p : Ideal R // p.IsMaximal}) (a c : ℕ), Nat.card (R ⧸ w.1) ^ (a + c) =
            Nat.card (R ⧸ w.1) ^ a * Nat.card (R ⧸ w.1) ^ c := fun _ _ _ => pow_add _ _ _
        rw [Finsupp.prod_add_index'
            (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) hz ha,
          Finsupp.prod_single_index
            (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) (hz _),
          pow_one, ← hmul, hk1c, hCAcard]
end Formalism.LFunctionChainParameters.LLcv
