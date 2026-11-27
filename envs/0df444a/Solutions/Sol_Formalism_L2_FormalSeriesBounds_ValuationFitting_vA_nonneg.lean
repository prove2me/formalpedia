-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationFitting.vA_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:06.382747+00:00
-- url     : https://prove2.me/submissions/f8135328-5754-4b80-b835-7332d976c0da

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_DualLattices_U10
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_vA_apply
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.ValuationFitting
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks
variable {C : Type} [Field C]
variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace Formalism.L2.FormalSeriesBounds.ValuationFitting
theorem _root_.solution (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) : ∀ x : R, 0 ≤ vA V R x := by
  intro x
  rw [vA_apply]
  by_cases hx : algebraMap R C x = 0
  · rw [hx, V.v.map_zero]; exact le_top
  · obtain ⟨t, ht1, ht2⟩ := hT _ hx
    rw [ht1]
    have hle : (vm (algebraMap R C x) : ℝ) ≤ 1 := by exact_mod_cast hv.map_le_one x
    have : 0 ≤ t := by
      by_contra hneg
      have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (not_le.mp hneg)
      rw [← ht2] at this
      linarith
    exact_mod_cast this
end Formalism.L2.FormalSeriesBounds.ValuationFitting
