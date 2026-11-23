-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.divisor_square_weight_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:57.234539+00:00
-- url     : https://prove2.me/submissions/40c1824c-0c0f-4b33-a4e8-cdedceb4b286

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_sqSet
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_nonneg
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_mul
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_coeffs
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_injective
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (hM : SqMassLeOne) (K : Type) [Field K] [Fintype K] (N : ℕ) (h : K[X])
    (hmon : h.Monic) (hdeg : h.natDegree ≤ N) (S : Finset (Fin N → K))
    (hS : ∀ c ∈ S, c ∈ sqSet K N ∧ h ∣ monicOf c) :
    ∑ c ∈ S, sqWeight (monicOf c) ≤ sqWeight h := by
  classical
  set M := N - h.natDegree with hMdef
  let φ : (Fin N → K) → (Fin M → K) := fun c i => (monicOf c / h).coeff i
  have hmul : ∀ c ∈ S, h * (monicOf c / h) = monicOf c := fun c hc =>
    EuclideanDomain.mul_div_cancel' hmon.ne_zero (hS c hc).2
  have hqmon : ∀ c ∈ S, (monicOf c / h).Monic := fun c hc =>
    hmon.of_mul_monic_left (by rw [hmul c hc]; exact monicOf_monic c)
  have hqdeg : ∀ c ∈ S, (monicOf c / h).natDegree = M := by
    intro c hc
    have h1 := hmon.natDegree_mul (hqmon c hc)
    rw [hmul c hc, monicOf_natDegree] at h1
    omega
  have hφ : ∀ c ∈ S, monicOf (φ c) = monicOf c / h := fun c hc =>
    monicOf_coeffs (hqmon c hc) (hqdeg c hc)
  have hφmem : ∀ c ∈ S, φ c ∈ sqSet K M := by
    intro c hc
    have hc' := (mem_sqSet c).mp (hS c hc).1
    rw [mem_sqSet, hφ c hc]
    refine ⟨hc'.1.squarefree_of_dvd ⟨h, by rw [mul_comm, hmul c hc]⟩, ?_⟩
    intro h0
    apply hc'.2
    rw [← hmul c hc, Polynomial.mul_coeff_zero, h0, mul_zero]
  have hinj : Set.InjOn φ (S : Set (Fin N → K)) := by
    intro c1 h1 c2 h2 he
    apply monicOf_injective
    rw [← hmul c1 h1, ← hmul c2 h2, ← hφ c1 h1, ← hφ c2 h2, he]
  have hw : ∀ c ∈ S, sqWeight (monicOf c) = sqWeight h * sqWeight (monicOf (φ c)) := by
    intro c hc
    rw [hφ c hc, ← sqWeight_mul _ _ hmon.ne_zero (hqmon c hc).ne_zero, hmul c hc]
  rw [Finset.sum_congr rfl hw, ← Finset.mul_sum]
  have h1 : ∑ c ∈ S, sqWeight (monicOf (φ c)) ≤ 1 := by
    rw [← Finset.sum_image (f := fun c' => sqWeight (monicOf c')) hinj]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hM K M)
    · intro c' hc'
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
      exact hφmem c hc
    · intro c' _ _
      exact sqWeight_nonneg _
  calc sqWeight h * ∑ c ∈ S, sqWeight (monicOf (φ c)) ≤ sqWeight h * 1 :=
        mul_le_mul_of_nonneg_left h1 (sqWeight_nonneg h)
    _ = sqWeight h := mul_one _
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
