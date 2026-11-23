-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.markov_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:52.696902+00:00
-- url     : https://prove2.me/submissions/01a6ab25-28e1-4a05-a2d5-92435a666ef3

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_markov_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Polynomial
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.E.AMarkov := by
  intro p d M hp hM x hx
  rcases eq_or_ne d 0 with rfl | hd
  · rw [eq_C_of_natDegree_le_zero hp]; simp
  · rcases le_total 0 x with h | h
    · exact Markov.markov_nonneg p d hd hp M hM x h hx.2
    · have hq : (p.comp (-X)).natDegree ≤ d := by
        refine natDegree_comp_le.trans ?_
        rw [natDegree_neg, natDegree_X, mul_one]; exact hp
      have hMq : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(p.comp (-X)).eval y| ≤ M := by
        intro y hy
        rw [eval_comp]
        refine hM _ ?_
        simp only [eval_neg, eval_X]
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have := Markov.markov_nonneg (p.comp (-X)) d hd hq M hMq (-x) (by linarith) (by linarith [hx.1])
      rw [derivative_comp] at this
      simpa using this
end Formalism.FourierDecayAlt.P
