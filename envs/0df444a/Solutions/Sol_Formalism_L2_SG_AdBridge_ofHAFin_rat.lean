-- Prove2me | solution 1 for Formalism.L2.SG.AdBridge.ofHAFin_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:31.80312+00:00
-- url     : https://prove2.me/submissions/c610ab61-c895-400f-8f9a-de3de6062d91

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
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



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
variable (I : AutInst)
namespace Formalism.L2.SG.AdBridge
theorem _root_.solution (h : HAd I) (γ : GL (Fin I.n) I.E)
    (hγ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h =
      Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ) :
    ofHAFin I h = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
  have hh : hmat I h = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := by
    first
      | (unfold hmat; rw [hγ]; rfl)
      | (simp only [hmat, hγ]; rfl)
      | (simp only [hmat, hγ]; done)
      | (rw [show hmat I h = ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h :
          GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) :
          Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) from rfl, hγ]; rfl)
  unfold ofHAFin
  rw [hh]
  ext i j
  simp only [Matrix.map_apply]
  exact tauF_inclR I _
end Formalism.L2.SG.AdBridge
