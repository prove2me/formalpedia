-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.character_additive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:33.837849+00:00
-- url     : https://prove2.me/submissions/1618c699-6800-4a85-8e6c-969c3afa3293

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.CharAdditive := by
  intro n p q
  have key : ∀ p q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUpperUni p → IsUpperUni q →
      superSum (p * q) = superSum p + superSum q := by
    intro p q hp hq
    simp only [superSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply]
    have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ).ne
    rw [Finset.sum_eq_add i.castSucc i.succ hne]
    · rw [hp.1, hq.1]; ring
    · intro k _ hk
      rcases lt_trichotomy k i.castSucc with h | h | h
      · rw [hp.2 _ _ h]; ring
      · exact absurd h hk.1
      · have : i.succ < k := by
          rcases lt_or_eq_of_le (Fin.castSucc_lt_iff_succ_le.1 h) with h' | h'
          · exact h'
          · exact absurd h'.symm hk.2
        rw [hq.2 _ _ this]; ring
    · simp
    · simp
  refine ⟨key p q, fun hp hq => ?_⟩
  have := key qᵀ pᵀ hq hp
  have e : ∀ l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, subSum l = superSum lᵀ := fun l => rfl
  rw [e, e, e, Matrix.transpose_mul, this]; ring
end Formalism.FourierDecayAlt.P
