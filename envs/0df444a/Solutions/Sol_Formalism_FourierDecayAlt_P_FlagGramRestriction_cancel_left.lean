-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.cancel_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:41:03.555303+00:00
-- url     : https://prove2.me/submissions/1c4210c9-a8af-4004-8adb-59b53d415c50

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction

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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagGramRestriction
theorem _root_.solution {m : Type*} [Fintype m] [DecidableEq m] (A X Y : Matrix m m ℂ) (hA : IsUnit A.det)
    (h : A * X = A * Y) : X = Y := by
  calc X = A⁻¹ * (A * X) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    _ = A⁻¹ * (A * Y) := by rw [h]
    _ = Y := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.FlagGramRestriction
