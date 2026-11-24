-- Prove2me | solution 1 for Formalism.L2.SG.AdBridge.ofHAFin_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:38.614869+00:00
-- url     : https://prove2.me/submissions/4513209d-08e9-4f87-925f-6627ec118bf6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Theorems.Thm_Formalism_L2_SG_AdBridge_tauF_tmul
import Theorems.Thm_Formalism_L2_SG_AdBridge_tauF_inclR
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


section
noncomputable section
namespace Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
variable (I : AutInst)
private theorem tauF_sigR_comm (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    tauF I (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig x) =
      Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (tauF I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig (a ⊗ₜ[I.F] y) =
        a ⊗ₜ[I.F] I.cm.sig y := rfl
    rw [hs, tauF_tmul, tauF_tmul]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]
end Formalism.L2.SG.AdBridge
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
variable (I : AutInst)
namespace Formalism.L2.SG.AdBridge
theorem _root_.solution (h : HAd I) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (ofHAFin I h) *
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * ofHAFin I h =
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
  have hM : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) (hmat I h) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * hmat I h =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J := h.2
  have h1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig)
      (hmat I h)).map (tauF I) =
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (ofHAFin I h) := by
    ext i j
    simp only [Formalism.UG.cT, ofHAFin, Matrix.map_apply, Matrix.transpose_apply]
    exact tauF_sigR_comm I _
  have h2 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (tauF I) =
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
    ext i j
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]
    exact tauF_inclR I _
  have h3 := congrArg (fun X => X.map (tauF I)) hM
  simp only [Matrix.map_mul] at h3
  rw [h1, h2] at h3
  exact h3
end Formalism.L2.SG.AdBridge
