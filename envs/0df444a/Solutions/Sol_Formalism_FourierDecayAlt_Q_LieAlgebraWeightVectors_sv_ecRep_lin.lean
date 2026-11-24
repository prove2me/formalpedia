-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_ecRep_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:08.255611+00:00
-- url     : https://prove2.me/submissions/808e1e2f-738d-4859-920b-9dd03b01378e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_dRep_lin

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
theorem _root_.solution (hall : ∀ v : Wp, v ∈ SmVec k r z π) {Z : Mx k r}
    (h1 : inLieW k r z (hpart1 (Hpk k r) Z)) (h2 : inLieW k r z (hpart2 (Hpk k r) Z)) :
    IsLinearMap ℂ (EcRep (Hpk k r) π Z) := by
  have l1 := sv_dRep_lin hall h1
  have l2 := sv_dRep_lin hall h2
  constructor
  · intro x y
    unfold EcRep
    rw [l1.map_add, l2.map_add, smul_add]
    abel
  · intro c x
    unfold EcRep
    rw [l1.map_smul, l2.map_smul, smul_add, smul_comm Complex.I c]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
