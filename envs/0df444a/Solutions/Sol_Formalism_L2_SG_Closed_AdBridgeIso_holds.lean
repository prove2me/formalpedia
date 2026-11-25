-- Prove2me | solution 1 for Formalism.L2.SG.Closed.AdBridgeIso_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:50:39.132999+00:00
-- url     : https://prove2.me/submissions/d0c254bf-c45d-4a20-963e-1c9fb008f1da

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_JRMapTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_ExistsNotMemRange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_ContinuousOfHAInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFinInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_BridgeMaxCpt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_BridgeRatPts
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedVolumeStatements_AdelicIsomorphismStatement
import Theorems.Thm_Formalism_L2_SG_Pf_adelic_isomorphism_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Closed
namespace Formalism.L2.SG.Closed
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeIso I :=
  Formalism.L2.SG.Pf.adelic_isomorphism_exists (I := I)
end Formalism.L2.SG.Closed
