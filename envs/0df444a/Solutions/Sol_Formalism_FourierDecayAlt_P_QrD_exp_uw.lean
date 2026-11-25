-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QrD.exp_uw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:38:48.727996+00:00
-- url     : https://prove2.me/submissions/2747f4c4-9a2b-4098-a7b7-ef9bc14d8982

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_exp_fix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.QrD
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {X : Mx k r} (hX : InLieW k r z X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UWset k r z := by
  have h := Qx8.exp_lev hX.1 t
  exact ⟨h.1, fun a => h.2 a (by simp), Qx8.exp_fix hX.2 t⟩
end Formalism.FourierDecayAlt.P.QrD
