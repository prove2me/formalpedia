-- Prove2me | solution 1 for CompanionTheory.D.LK.sum_tc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:23.062803+00:00
-- url     : https://prove2.me/submissions/de6901aa-c65b-4a74-a1b3-1a973d2e1f6b

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
import Theorems.Thm_CompanionTheory_D_LK_tri_uniq
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
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (i j : Pos n) (f : Pos n → M) :
    ∑ k, tc ε i j k • f k = if h : cpt ε i ∧ cpt ε j ∧ i.1.2 = j.1.1 then
      f ⟨(i.1.1, j.1.2), i.2.trans (h.2.2 ▸ j.2)⟩ else 0 := by
  split_ifs with h
  · have ht : Tri ε i j ⟨(i.1.1, j.1.2), i.2.trans (h.2.2 ▸ j.2)⟩ := ⟨h.1, h.2.1, h.2.2, rfl, rfl⟩
    rw [Finset.sum_eq_single _ (fun k _ hk => by rw [tc, if_neg fun h' => hk (tri_uniq h' ht), zero_smul]) (by simp),
      tc, if_pos ht, one_smul]
  · exact Finset.sum_eq_zero fun k _ => by rw [tc, if_neg fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩, zero_smul]
end CompanionTheory.D.LK
