-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.cell_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:10.066812+00:00
-- url     : https://prove2.me/submissions/4055e092-ef02-4fa6-986b-395849f4a745

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_psi_nonneg
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_psi_sum_le
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_tsum_psi_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution (f : ℕ) (P : Finset (Fin f → ℤ × ℤ)) :
    ∑ p ∈ P, ∏ v, (psi (p v).1 * psi (p v).2) ≤ ((∑' n, psi n) ^ 2) ^ f := by
  classical
  set T : Finset ℤ := (P.biUnion fun p => univ.image fun v => (p v).1) ∪
    (P.biUnion fun p => univ.image fun v => (p v).2) with hT
  have hsub : P ⊆ Fintype.piFinset (fun _ : Fin f => T ×ˢ T) := by
    intro p hp
    rw [Fintype.mem_piFinset]
    intro v
    rw [mem_product]
    constructor
    · apply mem_union_left
      exact mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨v, mem_univ _, rfl⟩⟩
    · apply mem_union_right
      exact mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨v, mem_univ _, rfl⟩⟩
  calc ∑ p ∈ P, ∏ v, (psi (p v).1 * psi (p v).2)
      ≤ ∑ p ∈ Fintype.piFinset (fun _ : Fin f => T ×ˢ T), ∏ v, (psi (p v).1 * psi (p v).2) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro p _ _
        exact prod_nonneg (fun v _ => mul_nonneg (psi_nonneg _) (psi_nonneg _))
    _ = ∏ _v : Fin f, ∑ q ∈ T ×ˢ T, psi q.1 * psi q.2 := by
        rw [prod_univ_sum]
    _ = ∏ _v : Fin f, ((∑ n ∈ T, psi n) * (∑ n ∈ T, psi n)) := by
        rw [sum_mul_sum, sum_product]
    _ ≤ ∏ _v : Fin f, ((∑' n, psi n) ^ 2) := by
        apply prod_le_prod
        · intro v _
          exact mul_nonneg (sum_nonneg fun n _ => psi_nonneg n) (sum_nonneg fun n _ => psi_nonneg n)
        · intro v _
          rw [sq]
          exact mul_le_mul (psi_sum_le T) (psi_sum_le T) (sum_nonneg fun n _ => psi_nonneg n)
            tsum_psi_nonneg
    _ = ((∑' n, psi n) ^ 2) ^ f := by
        rw [prod_const, card_univ, Fintype.card_fin]
end Formalism.NuclearRankWeightBounds.P
