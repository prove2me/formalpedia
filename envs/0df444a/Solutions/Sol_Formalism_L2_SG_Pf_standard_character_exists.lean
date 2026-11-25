-- Prove2me | solution 1 for Formalism.L2.SG.Pf.standard_character_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:39:49.383637+00:00
-- url     : https://prove2.me/submissions/43bac1e1-2098-489c-8a94-aeecfea04ba5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar
import Theorems.Thm_Formalism_L2_SG_Pf_StdChar_psiStd_isChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf
namespace Formalism.L2.SG.Pf
theorem _root_.solution : Formalism.L2.SG.Pf.MeasCore.StdCharExists := by
  intro F _ _ hF
  haveI := hF
  refine ⟨StdChar.psiStd F, StdChar.psiStd_isChar F, fun x => ?_⟩
  show StdChar.psiA F x * StdChar.psiFin F 0 = _
  rw [StdChar.psiFin_zero, mul_one]
  rfl
end Formalism.L2.SG.Pf
