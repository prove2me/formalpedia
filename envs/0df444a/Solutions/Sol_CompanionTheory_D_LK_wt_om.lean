-- Prove2me | solution 1 for CompanionTheory.D.LK.wt_om
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:04.972649+00:00
-- url     : https://prove2.me/submissions/b889517c-f5f7-4bcc-bdfc-e6b07a1ddc2d

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
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
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution (ε : Fin n → Bool) : wt (om ε) = (2 : ℝ) • PI.UpqRep.rhoC ε := by
  funext c
  simp only [wt, PI.UpqRep.rhoC, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_cancel₀ _ (two_ne_zero' ℝ)]
  congr 2
  · refine card_bij (fun i _ => i.1.2) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun b hb => ?_)
    · simp only [om, mem_filter, mem_univ, true_and] at hi ⊢
      exact ⟨hi.2 ▸ i.2, hi.2 ▸ hi.1.symm⟩
    · exact Subtype.ext (Prod.ext ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm) h)
    · simp only [mem_filter, mem_univ, true_and] at hb
      exact ⟨⟨(c, b), hb.1⟩, by simp [om, cpt, hb.2], rfl⟩
  · refine card_bij (fun i _ => i.1.1) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun b hb => ?_)
    · simp only [om, mem_filter, mem_univ, true_and] at hi ⊢
      exact ⟨hi.2 ▸ i.2, hi.2 ▸ hi.1⟩
    · exact Subtype.ext (Prod.ext h ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm))
    · simp only [mem_filter, mem_univ, true_and] at hb
      exact ⟨⟨(b, c), hb.1⟩, by simp [om, cpt, hb.2], rfl⟩
end CompanionTheory.D.LK
