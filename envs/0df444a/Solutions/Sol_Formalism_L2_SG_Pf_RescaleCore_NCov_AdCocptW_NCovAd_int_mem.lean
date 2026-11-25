-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW.NCovAd_int_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:41.813917+00:00
-- url     : https://prove2.me/submissions/74a8c663-c504-4e9b-b165-e61ea3d73f1a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_CompactCovering_NCovAd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Metric
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RescaleCore Formalism.L2.SG.Pf.RescaleCore.NCov
open Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
theorem _root_.solution (β : 𝓞 F) : algebraMap F (Af F) (β : F) ∈ Formalism.UG.intAd F := by
  show ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    (algebraMap F (Af F) (β : F)) v ∈ v.adicCompletionIntegers F
  intro v
  first
  | exact v.coe_mem_adicCompletionIntegers β
  | exact (v.mem_adicCompletionIntegers F).mpr (by
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using v.valuation_le_one β)
  | exact (v.mem_adicCompletionIntegers F).mpr (by
      show Valued.v ((β : F) : v.adicCompletion F) ≤ 1
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using v.valuation_le_one β)
end Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
