-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.card_eq_prod_locLen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:48:04.934036+00:00
-- url     : https://prove2.me/submissions/21e01011-e76a-4a40-ad56-6fc2e94b5b37

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_locLen_exact
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_locLen_congr
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_locLen_subsingleton
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_locLen_quot_ne
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_locLen_quot_self

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
variable {R : Type} [CommRing R]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q] [Finite Q],
    Nat.card Q = n → ∃ k : {p : Ideal R // p.IsMaximal} →₀ ℕ,
      (∀ w : {p : Ideal R // p.IsMaximal}, (haveI := w.2.isPrime; locLen w.1 Q) = (k w : ℕ∞)) ∧
      Nat.card Q = k.prod fun w j => Nat.card (R ⧸ w.1) ^ j := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ hn
  by_cases hQ : Subsingleton Q
  · refine ⟨0, fun w => ?_, ?_⟩
    · have := w.2.isPrime
      rw [locLen_subsingleton]; simp
    · rw [Finsupp.prod_zero_index]; exact Nat.card_of_subsingleton 0
  · rw [not_subsingleton_iff_nontrivial] at hQ
    rcases eq_top_or_exists_le_coatom (⊥ : Submodule R Q) with h | ⟨Q1, hQ1, -⟩
    · exact absurd h bot_ne_top
    · have hsimple : IsSimpleModule R (Q ⧸ Q1) := isSimpleModule_iff_isCoatom.2 hQ1
      obtain ⟨m0, hm0, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      have hnt : Nontrivial (Q ⧸ Q1) := IsSimpleModule.nontrivial R _
      have hcard : Nat.card Q = Nat.card Q1 * Nat.card (Q ⧸ Q1) :=
        Submodule.card_eq_card_quotient_mul_card Q1
      have hfq : Finite (Q ⧸ Q1) := Finite.of_surjective _ Q1.mkQ_surjective
      have h1 : 1 < Nat.card (Q ⧸ Q1) := Finite.one_lt_card
      have h2 : 0 < Nat.card Q1 := Nat.card_pos
      have hlt : Nat.card Q1 < n := by
        rw [← hn, hcard]; nlinarith
      obtain ⟨k1, hk1, hk1c⟩ := ih _ hlt Q1 rfl
      refine ⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩
      · have := w.2.isPrime
        have := w.2
        rw [locLen_exact w.1 Q1.subtype Q1.mkQ Q1.injective_subtype Q1.mkQ_surjective
          (LinearMap.exact_subtype_mkQ Q1), hk1 w, locLen_congr w.1 e, Finsupp.add_apply,
          Finsupp.single_apply]
        by_cases hw : (⟨m0, hm0⟩ : {p : Ideal R // p.IsMaximal}) = w
        · subst hw
          rw [if_pos rfl, locLen_quot_self]; simp
        · rw [if_neg hw, locLen_quot_ne w.1 m0 (fun h => hw (Subtype.ext h.symm))]; simp
      · have hz : ∀ w : {p : Ideal R // p.IsMaximal}, Nat.card (R ⧸ w.1) ^ 0 = 1 :=
          fun _ => pow_zero _
        have ha : ∀ (w : {p : Ideal R // p.IsMaximal}) (a c : ℕ), Nat.card (R ⧸ w.1) ^ (a + c) =
            Nat.card (R ⧸ w.1) ^ a * Nat.card (R ⧸ w.1) ^ c := fun _ _ _ => pow_add _ _ _
        rw [Finsupp.prod_add_index'
            (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) hz ha,
          Finsupp.prod_single_index
            (h := fun (w : {p : Ideal R // p.IsMaximal}) (j : ℕ) => Nat.card (R ⧸ w.1) ^ j) (hz _),
          pow_one, hcard, hk1c, Nat.card_congr e.toEquiv]
end Formalism.LFunctionChainParameters.slopeLatticeData
