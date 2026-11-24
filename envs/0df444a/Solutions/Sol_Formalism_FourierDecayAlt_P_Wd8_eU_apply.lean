-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.eU_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:08.963445+00:00
-- url     : https://prove2.me/submissions/f808b91e-eef7-469c-83c4-f28af5f858f1

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  simp only [eU, Matrix.of_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, funext fun b => ?_⟩
    by_cases hb : b = a
    · rw [hb]
      simp [h2]
    · simp [Function.update_apply, hb, h3 b hb]
  · rintro ⟨h1, rfl⟩
    exact ⟨h1, by simp, fun b hb => by simp [Function.update_apply, hb]⟩
end Formalism.FourierDecayAlt.P.Wd8
