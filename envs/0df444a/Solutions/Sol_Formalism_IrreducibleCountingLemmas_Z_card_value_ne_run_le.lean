-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.card_value_ne_run_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:57.7199+00:00
-- url     : https://prove2.me/submissions/45e182a9-1e50-428d-a978-39d4e97e530e

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
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
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ) (hpt : p + t ≤ n)
    (hrun : ∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) (c₀ : ℤ) (h : c₀ ≠ c) :
    (Finset.univ.filter fun j => lam j = c₀).card ≤ n - t := by
  have hcard : (Finset.univ.filter fun j : Fin n => lam j = c).card = t := by
    have : (Finset.univ.filter fun j : Fin n => lam j = c).map Fin.valEmbedding =
        Finset.Ico p (p+t) := by
      ext a
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_Ico]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact (hrun j).1 hj
      · intro h; exact ⟨⟨a, by omega⟩, (hrun _).2 h, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]; omega
  have hd : Disjoint (Finset.univ.filter fun j : Fin n => lam j = c₀)
      (Finset.univ.filter fun j : Fin n => lam j = c) := by
    rw [Finset.disjoint_filter]; intro j _ h1 h2; exact h (h1.symm.trans h2)
  have := Finset.card_le_univ ((Finset.univ.filter fun j : Fin n => lam j = c₀) ∪
      (Finset.univ.filter fun j : Fin n => lam j = c))
  rw [Finset.card_union_of_disjoint hd, hcard, Fintype.card_fin] at this
  omega
end Formalism.IrreducibleCountingLemmas.Z
