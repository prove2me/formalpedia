-- Prove2me | solution 1 for CompanionTheory.D.LK.koszul_differential_sq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:44.066333+00:00
-- url     : https://prove2.me/submissions/e51a5099-68df-434b-9622-54e14c238e89

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
import Theorems.Thm_CompanionTheory_D_LK_koszul_differential_sq
import Theorems.Thm_CompanionTheory_D_LK_koszul_differential_anticommutator
import Theorems.Thm_CompanionTheory_D_LK_beta_sq
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_ann
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_cre
import Theorems.Thm_CompanionTheory_D_LK_Car_cre_cre
import Theorems.Thm_CompanionTheory_D_LK_lift_ann
import Theorems.Thm_CompanionTheory_D_LK_lift_cre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.LK
theorem _root_.solution : BdSq := by
  intro n ε V _ _ E hE
  have e : bd ε E = (∑ i, cc ε i • ((lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i)) +
      ∑ i, ∑ j, ∑ k, tc ε i j k • (cre k * ann j * ann i : Module.End ℂ (Cn n V)) := by
    simp only [bd, cc, tc, ite_smul, one_smul, zero_smul]
  have hL : KRel ε fun a b => (lift n (E a b) : Module.End ℂ (Cn n V)) := by
    intro a b c d h1 h2
    refine LinearMap.ext fun x => funext fun A => ?_
    have := LinearMap.congr_fun (hE a b c d h1 h2) (x A)
    split_ifs at this ⊢ <;> simpa using this
  have h1 : ∀ a b i, Commute (lift n (E a b) : Module.End ℂ (Cn n V)) (ann i) :=
    fun a b i => LinearMap.ext fun y => lift_ann _ _ y
  have h2 : ∀ a b i, Commute (lift n (E a b) : Module.End ℂ (Cn n V)) (cre i) :=
    fun a b i => LinearMap.ext fun y => lift_cre _ _ y
  rw [e, add_mul, mul_add, mul_add, koszul_differential_sq _ ann hL h1 ann_ann, beta_sq ann cre ann_ann cre_cre ann_cre, add_zero,
    add_assoc, koszul_differential_anticommutator _ ann cre h1 h2 ann_ann ann_cre, add_neg_cancel]
end CompanionTheory.D.LK
