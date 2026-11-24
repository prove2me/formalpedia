-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.ec_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:30:36.854509+00:00
-- url     : https://prove2.me/submissions/1d05093b-b702-47b0-9bbc-acf2a84de662

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ElementaryGeneratorsLevelGroup
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart1_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart2_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_flow_of_lieL
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_lieL_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_sub


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
theorem _root_.solution {i : Fin (r + 1)} {A B : Mx k r} (hA : Good k r i A) (hB : Good k r i B)
    {f F : Mx k r → E} {U : Set (Mx k r)} (hL : LocExt (Glev k r i) f F U) {g : Mx k r}
    (hg : g ∈ U) (hgG : g ∈ Glev k r i) :
    Ec (A - B) f g = Ec A f g - Ec B f g := by
  simp only [Ec]
  rw [hpart1_sub, hpart2_sub,
    loc_sub (flow_of_lieL hA.1) (flow_of_lieL hB.1) (flow_of_lieL (lieL_sub hA.1 hB.1)) hL hg hgG,
    loc_sub (flow_of_lieL hA.2) (flow_of_lieL hB.2) (flow_of_lieL (lieL_sub hA.2 hB.2)) hL hg hgG,
    smul_sub]
  abel
end Formalism.FourierDecayAlt.Q.EabGlW
