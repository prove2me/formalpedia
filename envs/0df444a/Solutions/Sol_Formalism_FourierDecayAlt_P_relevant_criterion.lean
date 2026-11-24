-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.relevant_criterion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:41:55.586536+00:00
-- url     : https://prove2.me/submissions/a3f125c8-375e-4dca-83da-8946cdd1750a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_blk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_blk_w
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_chain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.RelevantCrit := by
  intro m w d
  constructor
  · intro hC
    refine ⟨blk w, blk_mono w, blk_w w, ?_, ?_⟩
    · intro a b hab hlt
      exact (chain w d hC a (b.val - a.val - 1) b (by rw [Fin.lt_def] at hlt; omega) hab).1
    · intro a b hab
      rcases lt_trichotomy a b with h | rfl | h
      · exact (chain w d hC a (b.val - a.val - 1) b (by rw [Fin.lt_def] at h; omega) hab).2
      · rfl
      · exact ((chain w d hC b (a.val - b.val - 1) a (by rw [Fin.lt_def] at h; omega) hab.symm).2).symm
  · rintro ⟨bl, hmono, hw, hrev, hd⟩ a b hab hwab
    have hsame : bl a = bl b := by
      apply le_antisymm (hmono (le_of_lt hab))
      rw [← hw a, ← hw b]; exact hmono (le_of_lt hwab)

    have hin : ∀ c : Fin m, a ≤ c → c ≤ b → bl c = bl a := by
      intro c h1 h2
      apply le_antisymm
      · rw [hsame]; exact hmono h2
      · exact hmono h1
    have hinv : ∀ c : Fin m, w b ≤ c → c ≤ w a → bl (w.symm c) = bl a := by
      intro c h1 h2
      have : bl c = bl a := by
        apply le_antisymm
        · rw [← hw a]; exact hmono h2
        · rw [hsame, ← hw b]; exact hmono h1
      rw [← hw (w.symm c), Equiv.apply_symm_apply, this]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => hd a b hsame⟩
    ·
      by_contra hne
      have hlt : (w b).val + 1 < (w a).val := by rw [Fin.lt_def] at hwab; omega
      set c : Fin m := ⟨(w b).val + 1, by omega⟩ with hc
      have hcb : bl (w.symm c) = bl a :=
        hinv c (by rw [Fin.le_def]; simp only [hc]; omega) (by rw [Fin.le_def]; simp only [hc]; omega)
      have hwc : w (w.symm c) = c := Equiv.apply_symm_apply w c

      have h1 : a < w.symm c := by
        rcases lt_trichotomy (w.symm c) a with h' | h' | h'
        · have := hrev (w.symm c) a (hcb.trans rfl) h'
          rw [hwc] at this; rw [Fin.lt_def] at this; simp only [hc] at this; omega
        · rw [← h', hwc] at hlt; simp only [hc] at hlt; omega
        · exact h'
      have h2 : w.symm c < b := by
        rcases lt_trichotomy (w.symm c) b with h' | h' | h'
        · exact h'
        · rw [h', hc] at hwc; have := congrArg Fin.val hwc; simp at this
        · have := hrev b (w.symm c) (hsame.symm.trans hcb.symm) h'
          rw [hwc] at this; rw [Fin.lt_def] at this; simp only [hc] at this; omega
      rw [Fin.lt_def] at h1 h2; omega
    ·
      by_contra hne
      have hlt : a.val + 1 < b.val := by rw [Fin.lt_def] at hab; omega
      set c : Fin m := ⟨a.val + 1, by omega⟩ with hc
      have hca : bl c = bl a := hin c (by rw [Fin.le_def]; simp only [hc]; omega)
        (by rw [Fin.le_def]; simp only [hc]; omega)
      have e1 := hrev a c hca.symm (by rw [Fin.lt_def]; simp only [hc]; omega)
      have e2 := hrev c b (hca.trans hsame) (by rw [Fin.lt_def]; simp only [hc]; omega)
      rw [Fin.lt_def] at e1 e2; omega
end Formalism.FourierDecayAlt.P
