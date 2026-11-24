-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_gram_ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:34:11.832775+00:00
-- url     : https://prove2.me/submissions/9c4307bb-7e25-4c5a-9449-47c61db0b829

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Theorems.Thm_Formalism_QuantumDeterminants_gn_Hpk_mulVec_lo
import Theorems.Thm_Formalism_QuantumDeterminants_gn_gramM_herm
import Theorems.Thm_Formalism_QuantumDeterminants_gn_herm_bvec_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    gramM k r z z' g (Sum.inl a) (Sum.inl b) =
      if a.val = r ∧ b.val = r then herm (Hpk k r) z z else 0 := by
  have hlo : ∀ a b : Fin (r + 1), a.val < r → gramM k r z z' g (Sum.inl a) (Sum.inl b) = 0 := by
    intro a b ha
    simp only [gramM, gramVec, fvec, ha, ↓reduceDIte]
    rw [gn_herm_bvec_right, gn_Hpk_mulVec_lo k r _ (eI k r ⟨a.val, ha⟩) ha]
    split_ifs with hb
    · simp only [bvec, Pi.single_apply, eI]
      rw [if_neg]
      intro e
      first | omega | (simp only [Fin.mk.injEq] at e; omega) | (have e' := Fin.val_eq_of_eq e; simp at e'; omega)
    · exact hz _ (Or.inr (by simp only [eI]; omega))
  have hA := a.isLt
  have hB := b.isLt
  by_cases ha : a.val < r
  · rw [hlo a b ha, if_neg (by omega)]
  · by_cases hb : b.val < r
    · have e := congrFun (congrFun (gn_gramM_herm k r z z' g) (Sum.inl a)) (Sum.inl b)
      rw [Matrix.conjTranspose_apply, hlo b a hb, star_zero] at e
      rw [← e, if_neg (by omega)]
    · have ha' : a.val = r := by omega
      have hb' : b.val = r := by omega
      rw [if_pos ⟨ha', hb'⟩]
      simp only [gramM, gramVec, fvec, ha, hb, ↓reduceDIte]
end Formalism.QuantumDeterminants
