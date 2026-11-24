-- Prove2me | solution 1 for Formalism.L2.SG.AdBridge.adBridgeGF_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:38:51.153678+00:00
-- url     : https://prove2.me/submissions/299a5729-1256-4071-9a58-3f8ee29b01c8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalPointsComparison_BridgeApplyEqOfComp
import Theorems.Thm_Formalism_L2_SG_AdBridge_bridge_apply_eq_of_comp
import Theorems.Thm_Formalism_L2_SG_AdBridge_bc_inclR_mem_HR
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
private theorem thetaV_inclR' (I : AutInst) (v : InfinitePlace I.F) (y : I.E) :
    thetaV I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) y) = I.φ v y := by
  simp [thetaV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
private theorem tauF_inclR' (I : AutInst) (y : I.E) :
    tauF I (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) y) = Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) y := by
  simp [tauF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.UG.inclE]
private theorem map_inclR_map_thetaV (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) I.E) :
    (M.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))).map (thetaV I v) = M.map (I.φ v) := by
  ext i j
  simp only [Matrix.map_apply, thetaV_inclR']
private theorem map_inclR_map_tauF (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) I.E) :
    (M.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))).map (tauF I) = M.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
  ext i j
  simp only [Matrix.map_apply, tauF_inclR']
end Formalism.L2.SG.AdBridge
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
namespace Formalism.L2.SG.AdBridge
theorem _root_.solution (I : AutInst) : AdBridgeGF I := by
  unfold AdBridgeGF
  intro e he
  ext h
  constructor
  · rintro ⟨x, hxG, rfl⟩
    obtain ⟨γ, hγ, hinf, hfin⟩ := hxG
    have hmem := bc_inclR_mem_HR I γ hγ
    let h0 : HAd I := (⟨Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ, hmem⟩ :
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J)
    have hm0 : hmat I h0 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := rfl
    have hx : e x = h0 := by
      apply bridge_apply_eq_of_comp I e he x h0
      · intro v
        rw [hinf v]
        unfold ofHAInf
        rw [hm0, map_inclR_map_thetaV]
      · rw [hfin]
        unfold ofHAFin
        rw [hm0, map_inclR_map_tauF]
    rw [hx]
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h0 ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J
    exact Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
  · intro hh
    have hh' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := hh
    obtain ⟨γ, hγ, hγh⟩ := Subgroup.mem_map.mp hh'
    have hm : hmat I h = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := by
      show ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h :
        GL (Fin I.n) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) ⊗[I.F] I.E)) = _
      rw [← hγh]
      rfl
    have hs : e (e.symm h) = h := by
      first
      | exact e.apply_symm_apply h
      | simp
    refine ⟨e.symm h, ?_, hs⟩
    simp only [Formalism.MainNotions.S.AutInst.GFset, Set.mem_setOf_eq]
    refine ⟨γ, hγ, fun v => ?_, ?_⟩
    · rw [(he (e.symm h)).1 v, hs]
      unfold ofHAInf
      rw [hm, map_inclR_map_thetaV]
    · rw [(he (e.symm h)).2, hs]
      unfold ofHAFin
      rw [hm, map_inclR_map_tauF]
end Formalism.L2.SG.AdBridge
