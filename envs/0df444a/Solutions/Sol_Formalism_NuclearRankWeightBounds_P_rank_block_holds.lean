-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.rank_block_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:20.305843+00:00
-- url     : https://prove2.me/submissions/738f1f95-42ce-46c8-abd8-f67f1856669f

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_RankLeOfSupport
import Theorems.Thm_P2M_Formalism_NuclearRankWeightBounds_P_rank_add_le__c793ac3f6c26
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_rank_le_of_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : Formalism.NuclearRankWeightBounds.D.RankBlock := by
  intro N ep Y hY
  classical
  set T := (univ : Finset (Fin N)).filter (fun a => ep a = true) with hT
  set F := (univ : Finset (Fin N)).filter (fun a => ep a = false) with hF
  set P : Matrix (Fin N) (Fin N) ℂ := diagonal (fun a => if ep a = true then 1 else 0) with hP
  set Q : Matrix (Fin N) (Fin N) ℂ := diagonal (fun a => if ep a = true then 0 else 1) with hQ
  have hsplit : Y = Y * P + Y * Q := by
    ext a b
    simp only [hP, hQ, Matrix.add_apply, Matrix.mul_diagonal]
    split_ifs <;> simp
  have h1 : (Y * P).rank ≤ min F.card T.card := by
    apply rank_le_of_support _ F T
    intro a b hab
    simp only [hP, Matrix.mul_diagonal] at hab
    cases hb : ep b
    · simp [hb] at hab
    · have hY' : Y a b ≠ 0 := by simpa [hb] using hab
      cases ha : ep a
      · simp [hT, hF, ha, hb]
      · exact absurd (hY a b (by rw [ha, hb])) hY'
  have h2 : (Y * Q).rank ≤ min T.card F.card := by
    apply rank_le_of_support _ T F
    intro a b hab
    simp only [hQ, Matrix.mul_diagonal] at hab
    cases hb : ep b
    · have hY' : Y a b ≠ 0 := by simpa [hb] using hab
      cases ha : ep a
      · exact absurd (hY a b (by rw [ha, hb])) hY'
      · simp [hT, hF, ha, hb]
    · simp [hb] at hab
  have h3 : Y.rank ≤ (Y * P).rank + (Y * Q).rank := by
    calc Y.rank = (Y * P + Y * Q).rank := congrArg Matrix.rank hsplit
      _ ≤ _ := rank_add_le' _ _
  have hq : Formalism.NuclearRankWeightBounds.D.q0 ep = min T.card F.card := rfl
  rw [hq]
  have := min_comm F.card T.card
  omega
end Formalism.NuclearRankWeightBounds.P
