-- Prove2me | solution 1 for Formalism.L2.SG.AdBridge.bridge_apply_eq_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:08.249817+00:00
-- url     : https://prove2.me/submissions/f51643e9-281a-4159-97e6-dd24bec59b9b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalPointsComparison_BridgeApplyEqOfComp
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
namespace Formalism.L2.SG.AdBridge
theorem _root_.solution (I : AutInst) (e : I.GA ≃ₜ* HAd I) (he : IsBridge I e)
    (x : I.GA) (h : HAd I) (h1 : ∀ v, uMat (x.1 v) = ofHAInf I h v)
    (h2 : I.fmat x.2 = ofHAFin I h) : e x = h := by
  have hs : e (e.symm h) = h := by
    first
    | exact e.apply_symm_apply h
    | simp
  have hB := he (e.symm h)
  rw [hs] at hB
  obtain ⟨h1', h2'⟩ := hB
  have hx : x = e.symm h := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact Subtype.ext (Units.ext ((h1 v).trans (h1' v).symm))
    · exact Subtype.ext (Units.ext (h2.trans h2'.symm))
  rw [hx, hs]
end Formalism.L2.SG.AdBridge
