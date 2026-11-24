-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_exp_uw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:41:05.663033+00:00
-- url     : https://prove2.me/submissions/512295a9-ba77-48f0-9ffa-75b1d2fb6cbd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_exp_mem
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
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {X : Mx k r} (hX : inLieW k r z X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UWset k r z :=
  ⟨B5.exp_mem hX.1 t, fun a => ⟨Qx2.exp_fix (hX.2.2 a).1 t, Qx2.exp_fix (hX.2.2 a).2 t⟩, Qx2.exp_fix hX.2.1 t⟩
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
