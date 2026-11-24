-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StdChar.ext_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:38:41.589862+00:00
-- url     : https://prove2.me/submissions/2d185d80-a376-4d5c-85e3-5942159ecf07

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StdChar
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace Formalism.L2.SG.Pf.StdChar
theorem _root_.solution (w : InfinitePlace F) (a : F) :
    InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) a) w) = w.embedding a := by
  first
    | exact InfinitePlace.Completion.extensionEmbedding_coe w a
    | simp [InfinitePlace.Completion.extensionEmbedding_coe]
    | rfl
end Formalism.L2.SG.Pf.StdChar
