-- Prove2me | solution 1 for CompanionTheory.D.LK.tc_assoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:48.19627+00:00
-- url     : https://prove2.me/submissions/50d67474-c481-40d7-bee8-bf00f949ae64

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
import Theorems.Thm_CompanionTheory_D_LK_sum_tc
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
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.LK
theorem _root_.solution (p q r k : Pos n) : ∑ i, tc ε p q i * tc ε i r k = ∑ j, tc ε q r j * tc ε p j k := by
  have h1 := sum_tc (ε := ε) p q (fun i => tc ε i r k)
  have h2 := sum_tc (ε := ε) q r (fun j => tc ε p j k)
  simp only [smul_eq_mul] at h1 h2
  rw [h1, h2]
  obtain ⟨⟨a, b⟩, _⟩ := p
  obtain ⟨⟨b', c⟩, _⟩ := q
  obtain ⟨⟨c', d⟩, _⟩ := r
  simp only [tc, Tri, cpt]
  by_cases hb : b = b'
  · subst hb
    by_cases hc : c = c'
    · subst hc
      simp only [dite_eq_ite]
      cases ε a <;> cases ε b <;> cases ε c <;> cases ε d <;> simp
    · simp [hc]
  · simp [hb]
end CompanionTheory.D.LK
