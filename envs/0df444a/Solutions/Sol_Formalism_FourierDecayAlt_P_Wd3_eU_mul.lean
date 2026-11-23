-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd3.eU_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:50.653977+00:00
-- url     : https://prove2.me/submissions/d386a224-5dac-49eb-b42b-567e9978322f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd3
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd3
theorem _root_.solution (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x a j)]
  · by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      simp only [eU, Matrix.of_apply]
      by_cases hx : x a = i <;> by_cases hy : y a = l <;> by_cases hxy : ∀ b, b ≠ a → x b = y b <;>
        simp (config := {contextual := true}) [Function.update_apply, hx, hy, hxy]
    · rw [if_neg hjk]
      simp [eU, Function.update_apply, hjk]
  · intro z _ hz
    simp only [eU, Matrix.of_apply]
    rw [if_neg, zero_mul]
    rintro ⟨_, h2, h3⟩
    apply hz
    funext b
    by_cases hb : b = a
    · subst hb
      simp [h2]
    · rw [Function.update_of_ne hb]
      exact (h3 b hb).symm
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.Wd3
