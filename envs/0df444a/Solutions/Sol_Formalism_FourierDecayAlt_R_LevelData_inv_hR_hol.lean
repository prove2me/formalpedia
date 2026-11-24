-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.LevelData.inv_hR_hol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:11.881433+00:00
-- url     : https://prove2.me/submissions/1c4d74d9-ae74-4e73-b4de-b8de05cd2364

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_cb
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_c
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_ci
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__i_46b19cb3119f
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_GG
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_S_mem
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_S_prod
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_Dr_Dri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.R.PInv
namespace _root_.Formalism.FourierDecayAlt.R.LevelData
theorem _root_.solution (Y : ℂ) :
    L.G * L.Di * L.Di * L.Ahat Y = L.Drb * L.GG * (L.ζi * L.ζi * L.Ar Y) := by
  letI : CommRing (Algebra.adjoin ℂ L.fns) := Algebra.adjoinCommRingOfComm ℂ L.fns_comm
  let Dr' : Algebra.adjoin ℂ L.fns := ⟨L.Dr, L.inv_S_prod L.inv_mem_c⟩
  let Drb' : Algebra.adjoin ℂ L.fns := ⟨L.Drb, L.inv_S_prod L.inv_mem_cb⟩
  let Dri' : Algebra.adjoin ℂ L.fns := ⟨L.Dri, L.inv_S_prod L.inv_mem_ci⟩
  let GG' : Algebra.adjoin ℂ L.fns := ⟨L.GG, L.inv_S_mem L.inv_mem_GG⟩
  let z' : Algebra.adjoin ℂ L.fns := ⟨L.ζi, L.inv_S_mem L.inv_mem_ζi⟩
  have h1 : Dr' * Dri' = 1 := Subtype.ext L.inv_Dr_Dri
  have hS : Dr' * Drb' * GG' * (z' * Dri') * (z' * Dri') * Dr' = Drb' * GG' * (z' * z') := by
    linear_combination (Drb' * GG' * z' * z' * (Dr' * Dri' + 1)) * h1
  have hA := congrArg Subtype.val hS
  simp only [LevelData.G, LevelData.Di, LevelData.Ahat]
  calc L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * (L.Dr * L.Ar Y)
      = (L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * L.Dr) * L.Ar Y := by
        noncomm_ring
    _ = (L.Drb * L.GG * (L.ζi * L.ζi)) * L.Ar Y := by rw [show L.Dr * L.Drb * L.GG * (L.ζi * L.Dri) * (L.ζi * L.Dri) * L.Dr = L.Drb * L.GG * (L.ζi * L.ζi) from hA]
    _ = L.Drb * L.GG * (L.ζi * L.ζi * L.Ar Y) := by noncomm_ring
end _root_.Formalism.FourierDecayAlt.R.LevelData
end Formalism.FourierDecayAlt.R.PInv
