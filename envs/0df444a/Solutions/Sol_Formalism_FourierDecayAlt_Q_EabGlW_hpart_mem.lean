-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.hpart_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:29:23.593847+00:00
-- url     : https://prove2.me/submissions/54f72728-b502-4267-8414-324da6726d5a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_skew_hpart1
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_skew_hpart2
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart_kill
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_out_eI
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_out_esI

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
theorem _root_.solution {i : Fin (r + 1)} {Z : Mx k r} (hZ : InV k r i Z) :
    hpart1 (Hpk k r) Z ∈ LieL k r i ∧ hpart2 (Hpk k r) Z ∈ LieL k r i :=
  ⟨⟨skew_hpart1 Z, fun a ha => ⟨(hpart_kill hZ (out_eI a ha)).1, (hpart_kill hZ (out_esI a ha)).1⟩⟩,
    ⟨skew_hpart2 Z, fun a ha => ⟨(hpart_kill hZ (out_eI a ha)).2, (hpart_kill hZ (out_esI a ha)).2⟩⟩⟩
end Formalism.FourierDecayAlt.Q.EabGlW
