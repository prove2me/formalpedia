-- Prove2me | solution 1 for CompanionTheory.D.Upq.ModEx.modProps_modD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:19.256997+00:00
-- url     : https://prove2.me/submissions/d40dd329-11e0-4330-929d-bbdf2bb27013

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_modular_aut
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_modular_bdd
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_modD_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.ModEx
open PI PI.QuotSetU.UnitaryGroupMassFormula
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
namespace CompanionTheory.D.Upq.ModEx
theorem _root_.solution (hG : IsMatGroup G) : ModProps G (modD hG) := by
  refine ⟨fun g hg => ?_, fun a ha b hb => ?_, fun c hc hn g hg => ?_, fun V hVG hV => ?_⟩
  · rw [modD_of_mem hg]; exact_mod_cast modularCharacterFun_pos _
  · rw [modD_of_mem ha, modD_of_mem hb, modD_of_mem (hG.2.2.1 a ha b hb), ← NNReal.coe_mul,
      ← modularCharacterFun_map_mul]
    rfl
  · rw [modD_of_mem hg, modD_of_mem ((hn g).2 hg),
      ← modular_aut (conjAut hG c hc hn) (MG.mk hG g hg)]
    rfl
  · obtain ⟨M, hM⟩ := modular_bdd ((MG.isClosedEmbedding_mat (hG := hG)).isCompact_preimage hV)
    refine ⟨M, fun v hv => ?_⟩
    rw [modD_of_mem (hVG hv)]
    exact hM _ hv
end CompanionTheory.D.Upq.ModEx
