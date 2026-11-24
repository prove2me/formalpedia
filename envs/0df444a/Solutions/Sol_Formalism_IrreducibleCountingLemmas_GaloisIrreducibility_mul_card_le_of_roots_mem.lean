-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mul_card_le_of_roots_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:51:00.67468+00:00
-- url     : https://prove2.me/submissions/74ee5c90-1d0b-454a-bac2-f454f143ba79

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_eq_of_common_root
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_frobenius_orbit_irreducible
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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {δ : ℕ} (F : Finset (Fin δ → K))
    (hF : ∀ c ∈ F, Irreducible (monicOf c)) (S : Finset L)
    (h : ∀ c ∈ F, ∀ x : L, aeval x (monicOf c) = 0 → x ∈ S) : δ * F.card ≤ S.card := by
  classical
  have hsub : F.biUnion (fun c => ((monicOf c).aroots L).toFinset) ⊆ S := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
    rw [Multiset.mem_toFinset, mem_aroots] at hxc
    exact h c hc x hxc.2
  have hdisj : (F : Set (Fin δ → K)).PairwiseDisjoint
      (fun c => ((monicOf c).aroots L).toFinset) := by
    intro a ha b hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxa hxb
    rw [Multiset.mem_toFinset, mem_aroots] at hxa hxb
    exact hab (eq_of_common_root (hF a ha) (hF b hb) hxa.2 hxb.2)
  have hcard : ∀ c ∈ F, (((monicOf c).aroots L).toFinset).card = δ := by
    intro c hc
    have := (frobenius_orbit_irreducible K L (monicOf c) (monicOf_monic c) (hF c hc)).2
    rw [monicOf_natDegree] at this
    convert this
  calc δ * F.card = ∑ c ∈ F, (((monicOf c).aroots L).toFinset).card := by
        rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = (F.biUnion (fun c => ((monicOf c).aroots L).toFinset)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ S.card := Finset.card_le_card hsub
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
