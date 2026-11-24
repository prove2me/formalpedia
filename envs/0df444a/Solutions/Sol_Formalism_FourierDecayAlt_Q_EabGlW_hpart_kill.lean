-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.hpart_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:31.050808+00:00
-- url     : https://prove2.me/submissions/d861ff3f-da74-4f7a-97d3-7e085bb61a0b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hinv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_col_HZH

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {i : Fin (r + 1)} {Z : Mx k r} (hZ : InV k r i Z) {q : Fin (2 * r + k + 1)}
    (hq : Out k r i q) :
    hpart1 (Hpk k r) Z *ᵥ bvec q = 0 ∧ hpart2 (Hpk k r) Z *ᵥ bvec q = 0 := by
  rw [mulVec_bvec, mulVec_bvec]
  refine ⟨funext fun p => ?_, funext fun p => ?_⟩ <;>
    simp only [hpart1, hpart2, hinv, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
      hZ p q (Or.inr hq), col_HZH hZ hq p, sub_zero, add_zero, smul_zero, Pi.zero_apply]
end Formalism.FourierDecayAlt.Q.EabGlW
