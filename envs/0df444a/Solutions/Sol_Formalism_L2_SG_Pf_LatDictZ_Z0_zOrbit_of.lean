-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.zOrbit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:11:02.601163+00:00
-- url     : https://prove2.me/submissions/02399e8f-6f66-4ab5-a39b-bf962af8cfdc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
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
open NumberField Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
namespace Formalism.L2.SG.Pf.LatDictZ.Z0
theorem _root_.solution (hZ : SemiGenusZ) (hA : AdelGlue) (hF : LocFinite) : ZOrbit := by
  intro I r s z M hMfg hMspan hMdual hsz hspan hsL hsM hzL hzM hpL hpM
  have hloc := fun (p : Ideal (𝓞 I.E)) (hp : p.IsMaximal) =>
    hZ I.E I.n I.J I.cm.cmUnram I.J_herm I.J_det s z I.L M I.L_fg hMfg I.L_span hMspan
      I.L_dual hMdual hsz hspan hsL hsM hzL hzM hpL hpM p hp
  choose γ hγU hγs hγz hγL using hloc
  obtain ⟨p₀, hp₀⟩ := Ideal.exists_maximal (𝓞 I.E)
  classical
  refine hA I s z M hMfg hMspan (hF I.E I.n I.L M I.L_fg hMfg I.L_span hMspan)
    (fun p => if hp : p.IsMaximal then γ p hp else γ p₀ hp₀) ?_ ?_ ?_ ?_
  · intro p
    by_cases hp : p.IsMaximal
    · simp only [dif_pos hp]; exact hγU p hp
    · simp only [dif_neg hp]; exact hγU p₀ hp₀
  · intro p a
    by_cases hp : p.IsMaximal
    · simp only [dif_pos hp]; exact hγs p hp a
    · simp only [dif_neg hp]; exact hγs p₀ hp₀ a
  · intro p
    by_cases hp : p.IsMaximal
    · simp only [dif_pos hp]; exact hγz p hp
    · simp only [dif_neg hp]; exact hγz p₀ hp₀
  · intro p hp v
    simp only [dif_pos hp]
    exact hγL p hp v
end Formalism.L2.SG.Pf.LatDictZ.Z0
