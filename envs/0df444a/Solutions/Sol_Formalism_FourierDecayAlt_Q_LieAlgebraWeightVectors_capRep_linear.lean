-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.capRep_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:45.66486+00:00
-- url     : https://prove2.me/submissions/98ac988c-0142-4ae9-b00a-5bc029f77f8b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_all
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_ecRep_lin
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_unitB_lie
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_qmF_lin

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
variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {u : ℕ → ℝ} (hπ : IsType k r z π u) {x₀ : Wp} (hx₀ : x₀ ≠ 0) (hsm : x₀ ∈ SmVec k r z π)
    {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hBs : IsFrameOf k r [z] Bs) (w : ℂ) :
    IsLinearMap ℂ (capRep k r π Bs w) := by
  have hall := sv_all hπ hx₀ hsm
  unfold capRep
  exact sv_qmF_lin _ (fun a b => sv_ecRep_lin hall (sv_unitB_lie hBs a b).1 (sv_unitB_lie hBs a b).2) id id w
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
