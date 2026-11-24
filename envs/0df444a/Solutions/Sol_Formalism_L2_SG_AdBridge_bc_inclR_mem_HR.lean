-- Prove2me | solution 1 for Formalism.L2.SG.AdBridge.bc_inclR_mem_HR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:21:27.202328+00:00
-- url     : https://prove2.me/submissions/baa2782d-a15a-48f2-8e32-ffad4cf911c6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalPointsComparison_BridgeApplyEqOfComp
import Theorems.Thm_Formalism_L2_SG_AdBridge_sigR_inclR_star
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
theorem _root_.solution (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := by
  have hγ' : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
  have key : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))) =
      (Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, sigR_inclR_star]
  show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J
  rw [key, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
end Formalism.L2.SG.AdBridge
