-- Prove2me | solution 1 for CompanionTheory.D.LK.tri_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:16.086022+00:00
-- url     : https://prove2.me/submissions/f31e97b7-8904-45c8-8fa7-50ef1371c44c

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Theorems.Thm_CompanionTheory_D_LK_ann_ne
import Theorems.Thm_CompanionTheory_D_LK_cre_ne

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
theorem _root_.solution {i j k : Pos n} {x : Cn n V} {A : Finset (Pos n)} (h : cre k (ann j (ann i x)) A ≠ 0) :
    k ∈ A ∧ j ∉ A.erase k ∧ i ∉ insert j (A.erase k) ∧ x (insert i (insert j (A.erase k))) ≠ 0 :=
  let h1 := cre_ne h
  let h2 := ann_ne h1.2
  let h3 := ann_ne h2.2
  ⟨h1.1, h2.1, h3.1, h3.2⟩
end CompanionTheory.D.LK
