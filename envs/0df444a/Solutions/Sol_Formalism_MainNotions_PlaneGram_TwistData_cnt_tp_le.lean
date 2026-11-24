-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cnt_tp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:52.317859+00:00
-- url     : https://prove2.me/submissions/ad377e0b-2985-468e-b925-10baf12f4df6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_le_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_first_embedding_ne_tangent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) :
    D.cnt j o (D.mtp (j, m)) ≤ ∑ a : Fin (D.nB j), if Fin.castAdd D.r a ∈ o then 1 else 0 := by
  by_cases hM : D.Marked j o
  · obtain ⟨l, hl, hln⟩ := hM
    refine le_trans (D.cnt_le_one j o _) ?_
    have : (if Fin.castAdd D.r (⟨l.val, hln⟩ : Fin (D.nB j)) ∈ o then 1 else 0 : ℕ) = 1 := by
      rw [if_pos]
      have : Fin.castAdd D.r (⟨l.val, hln⟩ : Fin (D.nB j)) = l := by ext; simp
      rw [this]; exact hl
    have h2 := Finset.single_le_sum (f := fun a : Fin (D.nB j) => if Fin.castAdd D.r a ∈ o then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨l.val, hln⟩ : Fin (D.nB j)))
    simp only [this] at h2
    exact h2
  · rw [D.cnt_zero j o]
    · exact Nat.zero_le _
    · intro l hl
      unfold fk at hl
      rw [if_neg hM] at hl
      exact D.first_embedding_ne_tangent j l _ hl
end Formalism.MainNotions.PlaneGram.TwistData
