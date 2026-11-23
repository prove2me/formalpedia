-- Prove2me | solution 1 for CompanionTheory.D.LK.differential_commutes_weight_operator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:06.090822+00:00
-- url     : https://prove2.me/submissions/f0a281b6-132c-411c-a9e7-d4f62cbb5811

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Theorems.Thm_CompanionTheory_D_LK_Ft_apply
import Theorems.Thm_CompanionTheory_D_LK_Ft_ann
import Theorems.Thm_CompanionTheory_D_LK_Ft_cre
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Tri_cptk
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
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution : ∀ (n : ℕ) (ε₀ ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), (∀ a b, ε a = ε b → ε₀ a = ε₀ b) → KRel ε E →
    ∀ c, Commute (Ft ε₀ E c) (bd ε E) := by
  intro n ε₀ ε V _ _ E h0 hE c
  refine Commute.add_right (Commute.sum_right _ _ _ fun i _ => ?_) (Commute.sum_right _ _ _ fun i _ =>
    Commute.sum_right _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ => ?_)
  · split_ifs with hi
    · refine LinearMap.ext fun x => ?_
      have e : ∀ y : Cn n V, Ft ε₀ E c (lift n (E i.1.1 i.1.2) y) =
          lift n (E i.1.1 i.1.2) (Ft ε₀ E c y) + (al i c : ℂ) • lift n (E i.1.1 i.1.2) y := by
        intro y
        funext A
        have := congrArg (fun T : Module.End ℂ V => T (y A)) (hE c c i.1.1 i.1.2 rfl hi)
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
        simp only [Ft_apply, lift_apply, Pi.add_apply, Pi.smul_apply, map_add, map_smul, sub_eq_iff_eq_add.1 this, al]
        have hne := i.2.ne
        by_cases h1 : c = i.1.1
        · subst h1; simp [hne.symm]; module
        · by_cases h2 : i.1.2 = c
          · subst h2; simp [hne, hne.symm]; module
          · simp [h1, h2, Ne.symm h1]
      simp only [Module.End.mul_apply]
      rw [e, Ft_ann E c (h0 _ _ hi), map_sub, map_smul, sub_add_cancel]
    · exact Commute.zero_right _
  · split_ifs with ht
    · refine LinearMap.ext fun x => ?_
      have hk := Tri.cptk (ε := ε) ht
      simp only [Module.End.mul_apply]
      rw [Ft_cre E c (h0 _ _ hk), Ft_ann E c (h0 _ _ ht.2.1), Ft_ann E c (h0 _ _ ht.1)]
      have : (al k c : ℂ) = al i c + al j c := by
        rw [← Complex.ofReal_add]; simp only [al, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2]; congr 1; ring
      simp only [map_sub, map_smul, this]
      module
    · exact Commute.zero_right _
end CompanionTheory.D.LK
