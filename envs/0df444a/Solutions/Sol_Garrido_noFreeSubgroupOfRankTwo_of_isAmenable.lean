-- Prove2me | solution 1 for Garrido.noFreeSubgroupOfRankTwo_of_isAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T20:32:35.952553+00:00
-- url     : https://prove2.me/submissions/90b84127-294e-4290-b329-b7ec29b1ac73

import Theorems.Thm_Garrido_exists_invariant_measure_and_not_isParadoxical_of_isAmenable
import Mathlib
import Theorems.Thm_Garrido_isParadoxical_freeGroup_and_isParadoxical_of_actsFreely
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Classes

universe u

namespace Garrido.BT

open scoped ENNReal Pointwise
open Set

/-! ### Reduced words -/

section Words

variable {α : Type*} [DecidableEq α]
set_option linter.unusedSectionVars false

end Words

/-! ### Equidecomposition lemmas (copied from proofs/EQ_Sec1.lean) -/

/-! ### The paradox from an equivariant map to `F₂` -/

abbrev F2 := FreeGroup (Fin 2)

theorem isParadoxical_of_actsFreely (X : Type*) [MulAction F2 X] [Nonempty X]
    (hfree : ActsFreely F2 X) : IsParadoxical F2 (Set.univ : Set X) :=
  (Garrido.isParadoxical_freeGroup_and_isParadoxical_of_actsFreely).2 X hfree

/-! ### Amenable groups have no free subgroup of rank two -/

theorem exists_invariant_measure_and_not_isParadoxical_of_isAmenable'
    {G : Type*} [Group G] (hG : IsAmenable G)
    (X : Type*) [MulAction G X] [Nonempty X] :
    (∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
        IsInvariant G m) ∧
      ¬ IsParadoxical G (Set.univ : Set X) :=
  by
  try haveI := hG; try haveI := X; first
    | exact Garrido.exists_invariant_measure_and_not_isParadoxical_of_isAmenable hG X
    | exact Garrido.exists_invariant_measure_and_not_isParadoxical_of_isAmenable
    | exact Garrido.exists_invariant_measure_and_not_isParadoxical_of_isAmenable ..
    | (apply Garrido.exists_invariant_measure_and_not_isParadoxical_of_isAmenable <;> first | assumption | infer_instance)
    | simpa using Garrido.exists_invariant_measure_and_not_isParadoxical_of_isAmenable


theorem noFreeSubgroupOfRankTwo_of_isAmenable' {G : Type*} [Group G] (hG : IsAmenable G) :
    Chou.NoFreeSubgroupOfRankTwo G := by
  intro f hf
  let _ : MulAction (FreeGroup (Fin 2)) G := MulAction.compHom G f
  have hfree : ActsFreely (FreeGroup (Fin 2)) G := by
    intro w x hw
    change f w * x = x at hw
    apply hf
    rw [map_one]
    exact mul_eq_right.1 hw
  have htrans : ∀ A B : Set G, Equidecomposable (FreeGroup (Fin 2)) A B →
      Equidecomposable G A B := by
    classical
    rintro A B ⟨e, rfl, rfl⟩
    refine ⟨⟨e.toPartialEquiv, e.witness.image f, fun a ha => ?_⟩, rfl, rfl⟩
    obtain ⟨w, hw, hwa⟩ := e.isDecompOn a ha
    exact ⟨f w, Finset.mem_image_of_mem f hw, hwa⟩
  obtain ⟨A, B, hA, hB, hAE, hBE, hAB, hAe, hBe⟩ := isParadoxical_of_actsFreely G hfree
  exact (exists_invariant_measure_and_not_isParadoxical_of_isAmenable' hG G).2
    ⟨A, B, hA, hB, hAE, hBE, hAB, htrans _ _ hAe, htrans _ _ hBe⟩

end Garrido.BT


namespace Garrido.BT

open Matrix

end Garrido.BT


namespace Garrido.BT

open Matrix

/-! ### Transfer of equidecompositions from an invariant subtype -/

section Transfer

open Set

variable {G H Y : Type*} [Group G] [MulAction G Y] [Group H]

end Transfer

/-! ### The sphere is uncountable -/

/-! ### Theorem 1.7 (Hausdorff) -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Real Matrix

/-! ## Part 2: absorbing a set with disjoint orbit translates -/

/-! ## Part 1: rotations -/

end Garrido.BT


namespace Garrido.BT

open scoped Pointwise
open Set

end Garrido.BT

namespace Garrido.BT

open Matrix

end Garrido.BT

namespace Garrido.BT

open Matrix Set
open scoped ENNReal Pointwise

end Garrido.BT


/-! Garrido, Corollary 1.10 (Banach–Tarski for balls and for ℝ³) and the p. 1 consequence. -/

namespace Garrido.BT
open scoped ENNReal Pointwise
open Set Matrix

/-! ## The radial projection -/

/-! ## Absorbing the centre -/

/-! ## The targets -/

end Garrido.BT


/-! ## Composition: every milestone, with no hypotheses -/

namespace Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem isParadoxical_freeGroup_and_isParadoxical_of_actsFreely :
    IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set (FreeGroup (Fin 2))) ∧
      ∀ (X : Type u) [MulAction (FreeGroup (Fin 2)) X] [Nonempty X],
        ActsFreely (FreeGroup (Fin 2)) X → IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set X) :=
  Garrido.isParadoxical_freeGroup_and_isParadoxical_of_actsFreely

theorem noFreeSubgroupOfRankTwo_of_isAmenable {G : Type*} [Group G] (hG : IsAmenable G) :
    Chou.NoFreeSubgroupOfRankTwo G :=
  Garrido.BT.noFreeSubgroupOfRankTwo_of_isAmenable' hG

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution {G : Type*} [Group G] (hG : IsAmenable G) :
    Chou.NoFreeSubgroupOfRankTwo G :=
  Garrido.BT.Final.noFreeSubgroupOfRankTwo_of_isAmenable hG
