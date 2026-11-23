-- Prove2me | solution 1 for CompanionTheory.D.LK.bd_sub_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:57.994479+00:00
-- url     : https://prove2.me/submissions/60f35c4c-328e-42a6-90e2-4ea30f0fa473

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
theorem _root_.solution {ε₀ ε : Fin n → Bool} (h0 : ∀ a b, ε a = ε b → ε₀ a = ε₀ b) (E : Fin n → Fin n → Module.End ℂ V)
    (x : Cn n V) (A : Finset (Pos n)) (h : bd ε₀ E x A ≠ bd ε E x A) :
    (∃ i, cpt ε₀ i ∧ ¬cpt ε i ∧ ann i x A ≠ 0) ∨
      ∃ i j k, Tri ε₀ i j k ∧ ¬(cpt ε i ∧ cpt ε j) ∧ cre k (ann j (ann i x)) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [bd_apply, bd_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : cpt ε i
    · rw [if_pos h1, if_pos (h0 _ _ h1)]
    · rw [if_neg h1]
      split_ifs with h2
      · rw [hc.1 i h2 h1, map_zero]
      · rfl
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : Tri ε i j k
    · rw [if_pos h1, if_pos ⟨h0 _ _ h1.1, h0 _ _ h1.2.1, h1.2.2⟩]
    · rw [if_neg h1]
      split_ifs with h2
      · exact hc.2 i j k h2 fun a b => h1 ⟨a, b, h2.2.2⟩
      · rfl
end CompanionTheory.D.LK
