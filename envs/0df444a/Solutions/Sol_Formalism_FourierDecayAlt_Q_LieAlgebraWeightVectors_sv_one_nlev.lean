-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_one_nlev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:46.675508+00:00
-- url     : https://prove2.me/submissions/e34883b7-4912-46cb-b9ef-40d63a6802c5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one
import Theorems.Thm_Formalism_QuantumDeterminants_nSubgroup


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
theorem _root_.solution (i : Fin (r + 1)) : (1 : Mx k r) ∈ Nlev k r i :=
  ⟨(nSubgroup k r).1, WeylGroupFacts.uh_one, fun _ _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩⟩
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
