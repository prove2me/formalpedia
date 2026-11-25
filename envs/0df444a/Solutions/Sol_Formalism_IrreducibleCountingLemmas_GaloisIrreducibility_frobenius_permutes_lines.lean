-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.frobenius_permutes_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:06:37.747034+00:00
-- url     : https://prove2.me/submissions/bf8ed780-3591-48e8-9375-8007031bf594

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : FrobPermutesLines := by
  intro k V ι _ _ _ _ _ t Φ g b c π hc ht hΦ hπ i
  have hpow : ∀ (n : ℕ) (j : ι), (t ^ n) (b j) = c j ^ n • b j := by
    intro n j
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, ht, smul_smul, ← pow_succ]
  have hw : (t ^ g) (Φ (b i)) = c i • Φ (b i) := by
    rw [← hΦ, ht, map_smul]
  have hcoord : ∀ j, (b.coord j) ∘ₗ (t ^ g) = c j ^ g • b.coord j := by
    intro j
    apply b.ext
    intro k
    simp only [LinearMap.comp_apply, hpow, map_smul, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs with h <;> simp [h]
  have hj : ∀ j, j ≠ π i → b.coord j (Φ (b i)) = 0 := by
    intro j hj
    have e1 := LinearMap.congr_fun (hcoord j) (Φ (b i))
    rw [LinearMap.comp_apply, hw, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at e1
    have hne : c j ^ g ≠ c i := by
      intro h
      apply hj
      have h2 := hπ (π.symm j)
      rw [Equiv.apply_symm_apply] at h2
      rw [h2] at h
      have h3 := hc h
      rw [← h3, Equiv.apply_symm_apply]
    have h4 : (c i - c j ^ g) * b.coord j (Φ (b i)) = 0 := by rw [sub_mul, e1, sub_self]
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hsum : Φ (b i) = b.repr (Φ (b i)) (π i) • b (π i) := by
    conv_lhs => rw [← b.sum_repr (Φ (b i))]
    rw [Finset.sum_eq_single (π i)]
    · intro j _ hj'
      rw [← Module.Basis.coord_apply, hj j hj', zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨b.repr (Φ (b i)) (π i), ?_, hsum⟩
  intro ha
  rw [ha, zero_smul] at hsum
  exact b.ne_zero i (Φ.injective (hsum.trans (map_zero Φ).symm))
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
