-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_mult_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.571816+00:00
-- url     : https://prove2.me/submissions/e56709a7-cee9-4072-805d-67512a74a25b

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
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
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Classical
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {K : Type} [Field K] [Fintype K] (N j : ℕ) (P : K[X]) (hP : P.Monic)
    (hj : P.natDegree = j) :
    ((Finset.univ : Finset (Fin N → K)).filter (fun c => P * P ∣ monicOf c)).card
      ≤ Fintype.card K ^ (N - 2 * j) := by
  have hPP : (P * P).Monic := hP.mul hP
  have hcard : Fintype.card (Fin (N - 2 * j) → K) = Fintype.card K ^ (N - 2 * j) := by simp
  rw [← hcard, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn
    (fun c => fun i : Fin (N - 2 * j) => ((monicOf c) /ₘ (P * P)).coeff i)
  · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · have key : ∀ c : Fin N → K, P * P ∣ monicOf c →
        ((monicOf c) /ₘ (P * P)).Monic ∧ ((monicOf c) /ₘ (P * P)).natDegree = N - 2 * j ∧
        monicOf c = P * P * ((monicOf c) /ₘ (P * P)) := by
      intro c hc
      obtain ⟨g, hg⟩ := hc
      have hdiv : (monicOf c) /ₘ (P * P) = g := by
        rw [hg]; exact mul_divByMonic_cancel_left g hPP
      have hgm : g.Monic := hPP.of_mul_monic_left (hg ▸ monicOf_monic c)
      have hdeg : (monicOf c).natDegree = (P * P).natDegree + g.natDegree := by
        rw [hg]; exact hPP.natDegree_mul hgm
      rw [monicOf_natDegree, hP.natDegree_mul hP, hj] at hdeg
      rw [hdiv]
      exact ⟨hgm, by omega, hg⟩
    intro c hc c' hc' h
    obtain ⟨h1, h2, h3⟩ := key c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
    obtain ⟨h1', h2', h3'⟩ := key c' (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
    apply monicOf_injective
    rw [h3, h3', ← monicOf_coeffs h1 h2, ← monicOf_coeffs h1' h2']
    exact congrArg (fun v => P * P * monicOf v) h
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
