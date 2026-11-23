-- Prove2me | solution 1 for CompanionTheory.D.LK.sum_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:24.924293+00:00
-- url     : https://prove2.me/submissions/5c212610-f09b-461d-8249-cf4ebb2f3dc4

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_FilterAll
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
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
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq lowK)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace CompanionTheory.D.LK
theorem _root_.solution {M : Type} [AddCommMonoid M] (f : Fin n → Fin n → M) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ i : Pos n, (f i.1.1 i.1.2 + f i.1.2 i.1.1) := by
  have h : ∀ g : Fin n → Fin n → M, ∑ i : Pos n, g i.1.1 i.1.2 = ∑ a, ∑ b, if a < b then g a b else 0 := fun g => by
    rw [← Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp) fun p => g p.1 p.2,
      Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_add_distrib, h f, h fun a b => f b a, Finset.sum_comm (f := fun a b => if a < b then f b a else 0),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, show f a a = ∑ b, if a = b then f a b else 0 by simp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.ne, h.not_gt]
  · simp [h]
  · simp [h, h.ne', h.not_gt]
end CompanionTheory.D.LK
