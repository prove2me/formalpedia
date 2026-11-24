-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.single_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:57:18.095342+00:00
-- url     : https://prove2.me/submissions/a2e2b5df-381d-4acf-b786-c1934eaa18a0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapAdInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (a b c d : Fin (2 * r + k + 1)) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) : Mat k r) := by
  split_ifs with h1 h2 h2
  all_goals
    first
    | (try subst h1); (try subst h2)
      simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, *]
    | ext i j
      simp_all [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul, Finset.sum_ite_eq,
        Finset.sum_ite_eq']
end Formalism.FourierDecayAlt.P.JFxE
