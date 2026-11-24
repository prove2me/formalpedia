-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.posL_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:17:28.100107+00:00
-- url     : https://prove2.me/submissions/5a7361fe-8362-4cb7-ae4a-8e55ee89ab6c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution {a b : Fin (mdim k r i)} (h : posL k r i a = posL k r i b) : a = b := by
  unfold posL at h
  have h2 := congrArg Fin.val h
  simp only at h2
  exact Fin.ext (by omega)
end Formalism.FourierDecayAlt.Q.TInvW
