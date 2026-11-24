-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.gmRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:36:04.52299+00:00
-- url     : https://prove2.me/submissions/da4d3c9e-985b-4351-a04b-4aa5481ee97a

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_Q
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_QQ
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_index_KK_le
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_index_ker_psi
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_KK_le_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open ModelEmbedding
open ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : GmRank := by
  intro n hn
  have hQ := card_Q n hn
  have hle : Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) ≤
      Nat.card (GalL n ⧸ Subgroup.zpowers (JJ n)) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  have h8 : 3 ≤ n → Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) = 8 := by
    intro h3
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [card_QQ]
    refine le_antisymm (index_KK_le m) ?_
    have hd : (psi m).ker.index ∣ (KK (m + 3)).index := Subgroup.index_dvd_of_le (KK_le_ker m)
    rw [index_ker_psi] at hd
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hd
  refine ⟨hQ, ?_, h8⟩
  rcases (by omega : n ≤ 2 ∨ 3 ≤ n) with h | h
  · refine hle.trans ?_
    rw [hQ]
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 := by norm_num
  · exact (h8 h).le
end Formalism.TwoAdicCyclotomicDecomposition
