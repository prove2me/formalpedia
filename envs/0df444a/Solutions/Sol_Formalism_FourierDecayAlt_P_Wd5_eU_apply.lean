-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd5.eU_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:04.897912+00:00
-- url     : https://prove2.me/submissions/812de7f8-f3cf-4fe7-ae7d-22b4981f111f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd5
open Matrix Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd5
theorem _root_.solution (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  have key : (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (x a = i ∧ y = Function.update x a j) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, funext fun b => ?_⟩
      by_cases hb : b = a
      · subst hb
        simp [h2]
      · simp only [Function.update_apply, if_neg hb]
        exact (h3 b hb).symm
    · rintro ⟨h1, rfl⟩
      exact ⟨h1, by simp, fun b hb => by simp [Function.update_apply, hb]⟩
  simp only [eU, Matrix.of_apply, key]
end Formalism.FourierDecayAlt.P.Wd5
