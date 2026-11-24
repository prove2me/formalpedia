-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StdChar.continuous_psiFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:42:09.170651+00:00
-- url     : https://prove2.me/submissions/d4feb118-9d13-46bb-bdab-d48fd406b243

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
theorem _root_.solution : Continuous (psiFin F) := by
  have hU : IsOpen ((Formalism.UG.intAd F : Set (Af F))) := by
    first
      | exact RestrictedProduct.isOpen_forall_mem (fun v => IsDedekindDomain.HeightOneSpectrum.isOpen_adicCompletionIntegers F v)
      | exact RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_integer _)
  have hf : Continuous ((exists_psiF F).choose) := by
    refine continuous_of_continuousAt_zero _ ?_
    rw [ContinuousAt, map_zero]
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [hU.mem_nhds (Formalism.UG.intAd F).zero_mem] with z hz
    exact (exists_psiF F).choose_spec.1 z hz
  have hc : Continuous (fun z : Af F => AddCircle.toCircle (-((exists_psiF F).choose z))) :=
    AddCircle.continuous_toCircle.comp hf.neg
  unfold psiFin
  first
    | exact continuous_subtype_val.comp hc
    | exact Circle.continuous_coe.comp hc
    | fun_prop
end Formalism.L2.SG.Pf.StdChar
