-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationFitting.lenCoker_eq_logb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:54.508902+00:00
-- url     : https://prove2.me/submissions/e73f1dd6-8210-4358-a65c-1ad302a2607e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_DualLattices_U10
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_vA_apply
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_vA_nonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_lenCoker_vA
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_lenCoker_le_of_mem
import Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_fitt_ge
import Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_fitt_le
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



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
    (h1 : (vm (V.l : C) : ℝ) < 1) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen vm R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) (hpos : 0 < (x : ℝ)) :
    S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) =
      ((Real.logb (vm (V.l : C) : ℝ) x : ℝ) : WithTop ℝ) := by
  have hxb : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x = x :=
    Real.rpow_logb h0 (ne_of_lt h1) hpos
  rw [← lenCoker_vA]
  apply le_antisymm
  · obtain ⟨y, hy, hyV⟩ := Formalism.MainNotions.G.ValuationFitting.fitt_ge hv α hx
    have hy0 : algebraMap R C y ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hyV
      rw [← hyV] at hpos
      simp at hpos
    obtain ⟨t, ht1, ht2⟩ := hT _ hy0
    refine le_trans (S4.lenCoker_le_of_mem (vA V R) (vA_nonneg hT hv h0 h1) _ hy) ?_
    rw [vA_apply, ht1]
    have : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x ≤ (vm (V.l : C) : ℝ) ^ t := by
      rw [hxb, ← ht2, hyV]
    rw [Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at this
    exact_mod_cast this
  · unfold S4.lenCoker
    refine Finset.le_inf fun g _ => ?_
    rw [vA_apply]
    by_cases hz : algebraMap R C (α.submatrix id g).det = 0
    · rw [hz, V.v.map_zero]; exact le_top
    · obtain ⟨t, ht1, ht2⟩ := hT _ hz
      rw [ht1]
      have hle : (vm (algebraMap R C (α.submatrix id g).det) : ℝ) ≤ x := by
        exact_mod_cast Formalism.MainNotions.G.ValuationFitting.fitt_le hv α hx g
      rw [ht2, ← hxb, Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at hle
      exact_mod_cast hle
end Formalism.L2.FormalSeriesBounds.ValuationFitting
