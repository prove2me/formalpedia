-- Prove2me | solution 1 for Formalism.L2.SG.AdBridge.ofHAInf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:09.935486+00:00
-- url     : https://prove2.me/submissions/2924cf6b-cfae-4242-bdc8-b547ecd58831

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Theorems.Thm_Formalism_L2_SG_AdBridge_thetaV_inclR
import Theorems.Thm_Formalism_L2_SG_AdBridge_thetaV_sigR
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
variable (I : AutInst)
namespace Formalism.L2.SG.AdBridge
theorem _root_.solution (h : HAd I) (v : InfinitePlace I.F) : Formalism.REAL.inUJ (I.ε v) (ofHAInf I h v) := by
  have hM : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) (hmat I h) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * hmat I h =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J := h.2
  have h1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig)
      (hmat I h)).map (thetaV I v) = ((hmat I h).map (thetaV I v))ᴴ := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    rw [thetaV_sigR, starRingEnd_apply]
  have h2 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (thetaV I v) =
      I.J.map (I.φ v) := by
    ext i j
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]
    exact thetaV_inclR I v _
  have hA : ((hmat I h).map (thetaV I v))ᴴ * I.J.map (I.φ v) * (hmat I h).map (thetaV I v) =
      I.J.map (I.φ v) := by
    have h3 := congrArg (fun X => X.map (thetaV I v)) hM
    simp only [Matrix.map_mul] at h3
    rw [h1, h2] at h3
    exact h3
  have hPu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have hPP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPu
  have hPPh : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one]
  unfold Formalism.REAL.inUJ ofHAInf
  rw [← I.P_spec v]
  calc _ = (I.P v)ᴴ * (((hmat I h).map (thetaV I v))ᴴ * (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) *
        I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) * (hmat I h).map (thetaV I v)) * I.P v := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (I.P v)ᴴ * (((hmat I h).map (thetaV I v))ᴴ * I.J.map (I.φ v) *
        (hmat I h).map (thetaV I v)) * I.P v := by
        rw [hPPh, hPP]
        simp only [Matrix.mul_one]
    _ = _ := by rw [hA]
end Formalism.L2.SG.AdBridge
