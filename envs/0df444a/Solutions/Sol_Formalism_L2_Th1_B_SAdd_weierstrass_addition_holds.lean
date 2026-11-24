-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.weierstrass_addition_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:00:09.536086+00:00
-- url     : https://prove2.me/submissions/74500c60-021b-4232-8f24-711547d4b36d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_sigma_rules_hold
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_atS_sq
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_sigma_addition_holds
import Theorems.Thm_Formalism_L2_Th1_B_Add0_triple_lintegral_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add1_triple_lintegral_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Formalism.L2.Th1.B.SAdd
theorem _root_.solution : WAdd := by
  intro K _ _ A kap w hw
  have H := sigma_addition_holds K A kap w hw
  obtain ⟨h1, -, -, h4, -, -⟩ := sigma_rules_hold K A kap w hw
  have E1 : ∀ i : Fin 2, at1 i w = at1 i (sW w) ^ 2 := by
    intro i
    have := congrArg (at1 i) h1
    simpa only [Add1.triple_lintegral_eq, map_pow] using this.symm
  have E4 : ∀ i : Fin 2, at1 i (dz w) = 2 * at1 i (sW w) * at1 i (dz (sW w)) := by
    intro i
    have := congrArg (at1 i) h4
    simpa only [Add1.triple_lintegral_eq, map_mul, map_ofNat] using this.symm
  have ES : atS w = atS (sW w) ^ 2 := by rw [← atS_sq, h1]
  rw [E1, E1] at H
  rw [ES, E4, E4, E1, E1]
  linear_combination (4 * at1 0 (sW w) ^ 2 * at1 1 (sW w) ^ 2 *
    (atS (sW w) * (1 - MvPowerSeries.C kap * at1 0 (sW w) ^ 2 * at1 1 (sW w) ^ 2) +
      (at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w))))) * H
end Formalism.L2.Th1.B.SAdd
