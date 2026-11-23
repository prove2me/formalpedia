-- Prove2me | solution 1 for CompanionTheory.D.LK.bd_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:28.618843+00:00
-- url     : https://prove2.me/submissions/cf69f46c-5f0f-411c-a22d-a4b35eb1c86f

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Theorems.Thm_CompanionTheory_D_LK_bd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (x : Cn n V) (A : Finset (Pos n))
    (h : bd ε E x A ≠ 0) :
    (∃ i, cpt ε i ∧ ann i x A ≠ 0) ∨ ∃ i j k, Tri ε i j k ∧ cre k (ann j (ann i x)) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h2
    · exact hc.2 i j k h2
    · rfl
  · intro i _
    split_ifs with h2
    · rw [hc.1 i h2, map_zero]
    · rfl
end CompanionTheory.D.LK
