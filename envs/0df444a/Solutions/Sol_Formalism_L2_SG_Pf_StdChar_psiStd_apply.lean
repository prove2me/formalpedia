-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StdChar.psiStd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:39:40.259295+00:00
-- url     : https://prove2.me/submissions/5a28e469-7a5a-4769-9b0b-ca6c50b6aaf8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StdChar
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace Formalism.L2.SG.Pf.StdChar
theorem _root_.solution (x : AF F) : psiStd F x = psiA F x.1 * psiFin F x.2 := rfl
end Formalism.L2.SG.Pf.StdChar
