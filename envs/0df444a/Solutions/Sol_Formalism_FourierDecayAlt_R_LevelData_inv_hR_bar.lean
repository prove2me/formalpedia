-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.LevelData.inv_hR_bar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:11.665676+00:00
-- url     : https://prove2.me/submissions/572cbe42-51cd-43a9-9758-0329c925cebf

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_cb
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_cbi
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_c
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__bi_b985a748edca
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_GG
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_S_mem
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_S_prod
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_Drb_Drbi

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
    L.G * L.Dbi * L.Dbi * L.Ahatv Y = L.Dr * L.GG * (L.ζbi * L.ζbi * L.Avr Y) := by
  letI : CommRing (Algebra.adjoin ℂ L.fns) := Algebra.adjoinCommRingOfComm ℂ L.fns_comm
  let Dr' : Algebra.adjoin ℂ L.fns := ⟨L.Dr, L.inv_S_prod L.inv_mem_c⟩
  let Drb' : Algebra.adjoin ℂ L.fns := ⟨L.Drb, L.inv_S_prod L.inv_mem_cb⟩
  let Drbi' : Algebra.adjoin ℂ L.fns := ⟨L.Drbi, L.inv_S_prod L.inv_mem_cbi⟩
  let GG' : Algebra.adjoin ℂ L.fns := ⟨L.GG, L.inv_S_mem L.inv_mem_GG⟩
  let z' : Algebra.adjoin ℂ L.fns := ⟨L.ζbi, L.inv_S_mem L.inv_mem_ζbi⟩
  have h1 : Drb' * Drbi' = 1 := Subtype.ext L.inv_Drb_Drbi
  have hS : Dr' * Drb' * GG' * (z' * Drbi') * (z' * Drbi') * Drb' = Dr' * GG' * (z' * z') := by
    linear_combination (Dr' * GG' * z' * z' * (Drb' * Drbi' + 1)) * h1
  have hA := congrArg Subtype.val hS
  simp only [LevelData.G, LevelData.Dbi, LevelData.Ahatv]
  calc L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * (L.Drb * L.Avr Y)
      = (L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * L.Drb) * L.Avr Y := by
        noncomm_ring
    _ = (L.Dr * L.GG * (L.ζbi * L.ζbi)) * L.Avr Y := by rw [show L.Dr * L.Drb * L.GG * (L.ζbi * L.Drbi) * (L.ζbi * L.Drbi) * L.Drb = L.Dr * L.GG * (L.ζbi * L.ζbi) from hA]
    _ = L.Dr * L.GG * (L.ζbi * L.ζbi * L.Avr Y) := by noncomm_ring
end _root_.Formalism.FourierDecayAlt.R.LevelData
end Formalism.FourierDecayAlt.R.PInv
