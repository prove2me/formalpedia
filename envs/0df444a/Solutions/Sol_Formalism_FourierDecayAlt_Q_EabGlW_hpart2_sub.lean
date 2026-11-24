-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.hpart2_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:48:02.408919+00:00
-- url     : https://prove2.me/submissions/7c27c836-85d6-47fa-8e32-01e26a9a6122

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ElementaryGeneratorsLevelGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution (A B : Mx k r) :
    hpart2 (Hpk k r) (A - B) = hpart2 (Hpk k r) A - hpart2 (Hpk k r) B := by
  simp only [hpart2, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_add]
  abel
end Formalism.FourierDecayAlt.Q.EabGlW
