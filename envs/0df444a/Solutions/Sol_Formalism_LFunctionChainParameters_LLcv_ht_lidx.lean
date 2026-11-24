-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.ht_lidx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:28:54.652892+00:00
-- url     : https://prove2.me/submissions/dcde327d-d4b6-428d-92ca-af1d8d44741a

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_indexLocLen_finsupp
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_span_inf
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_index
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_relIndex_ne_zero


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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {E M : Submodule (𝓞 K) V} (hE : E.FG) (hM : M.FG)
    (h : Submodule.span K (E : Set V) = Submodule.span K (M : Set V)) :
    (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; lidx p.1 E M)).Finite ∧
      Real.log (ht b X M) = Real.log (ht b X E) +
        ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, Real.log (Ideal.absNorm p.1 : ℝ) *
          (haveI := p.2.isPrime; (lidx p.1 E M : ℝ)) := by
  classical
  have hs := span_inf hE h
  have hrE : rkK (E ⊓ M) = rkK E := by unfold rkK; rw [hs]
  have hrM : rkK (E ⊓ M) = rkK M := by unfold rkK; rw [hs, h]
  have h1 := ht_index b X hX hE inf_le_left hrE
  have h2 := ht_index b X hX hM inf_le_right hrM
  have n1 := relIndex_ne_zero b X hX hE inf_le_left hrE
  have n2 := relIndex_ne_zero b X hX hM inf_le_right hrM
  obtain ⟨kE, hkE, hcE⟩ := indexLocLen_finsupp E (E ⊓ M) inf_le_left n1
  obtain ⟨kM, hkM, hcM⟩ := indexLocLen_finsupp M (E ⊓ M) inf_le_right n2
  have hl : ∀ w : {p : Ideal (𝓞 K) // p.IsMaximal},
      (haveI := w.2.isPrime; lidx w.1 E M) = (kE w : ℤ) - kM w := by
    intro w
    have a1 := hkE w
    have a2 := hkM w
    unfold pLen at a1 a2
    unfold lidx Formalism.HermitianLatticesTheory.locLen
    rw [a1, a2, ENat.toNat_natCast, ENat.toNat_natCast]
  have hsub : ∀ w : {p : Ideal (𝓞 K) // p.IsMaximal}, w ∉ kE.support ∪ kM.support →
      (haveI := w.2.isPrime; lidx w.1 E M) = 0 := by
    intro w hw
    rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hw
    rw [hl, hw.1, hw.2]; simp
  refine ⟨(kE.support ∪ kM.support).finite_toSet.subset fun w hw => ?_, ?_⟩
  · by_contra hc
    exact hw (hsub w hc)
  · rw [finsum_eq_sum_of_support_subset (s := kE.support ∪ kM.support)]
    · have e1 : ∑ w ∈ kE.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kE w : ℝ) =
          ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kE w : ℝ) :=
        Finset.sum_subset Finset.subset_union_left fun w _ hw => by
          rw [Finsupp.notMem_support_iff.1 hw]; simp
      have e2 : ∑ w ∈ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kM w : ℝ) =
          ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kM w : ℝ) :=
        Finset.sum_subset Finset.subset_union_right fun w _ hw => by
          rw [Finsupp.notMem_support_iff.1 hw]; simp
      have e3 : ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) *
          (haveI := w.2.isPrime; (lidx w.1 E M : ℝ)) =
          ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kE w : ℝ) -
          ∑ w ∈ kE.support ∪ kM.support, Real.log (Ideal.absNorm w.1 : ℝ) * (kM w : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hl]; push_cast; ring
      rw [e3, ← e1, ← e2, ← hcE, ← hcM]
      have l1 := congrArg Real.log h1
      have l2 := congrArg Real.log h2
      rw [Real.log_mul (ht_pos b X hX hE).ne' (by exact_mod_cast n1)] at l1
      rw [Real.log_mul (ht_pos b X hX hM).ne' (by exact_mod_cast n2)] at l2
      linarith
    · intro w hw
      by_contra hc
      apply hw
      show _ * _ = (0 : ℝ)
      rw [hsub w hc]; simp
end Formalism.LFunctionChainParameters.LLcv
