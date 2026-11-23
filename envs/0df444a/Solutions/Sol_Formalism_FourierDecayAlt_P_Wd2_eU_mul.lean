-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.eU_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:43.911015+00:00
-- url     : https://prove2.me/submissions/a4a7dc1f-bace-43e9-806a-c1dd3ffba20b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd2
theorem _root_.solution (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x z
  rw [Matrix.mul_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, Finset.sum_eq_single (Function.update x a j)]
    · simp (config := { contextual := true }) only [eU, Matrix.of_apply, Function.update_self,
        Function.update_apply, true_and, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
      by_cases hx : x a = i ∧ z a = l ∧ ∀ b, b ≠ a → x b = z b
      · simp [hx]
      · rw [if_neg hx]
        split_ifs <;> simp_all
    · intro y _ hy
      simp only [eU, Matrix.of_apply]
      split_ifs with h1 h2 <;> simp only [mul_one, mul_zero, zero_mul]
      exfalso
      apply hy
      funext b
      by_cases hb : b = a
      · subst hb
        rw [Function.update_self, h1.2.1]
      · rw [Function.update_of_ne hb, h1.2.2 b hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hjk, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    simp only [eU, Matrix.of_apply]
    split_ifs with h1 h2
    · exact absurd (h1.2.1.symm.trans h2.1) hjk
    all_goals simp
end Formalism.FourierDecayAlt.P.Wd2
