-- Prove2me | solution 1 for Garrido.equidecomposable_univ_compl_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:12:45.775833+00:00
-- url     : https://prove2.me/submissions/e88e841f-8159-4d6e-9cb7-2a9d3721c1f7

import Mathlib
import Theorems.Thm_Garrido_exists_disjoint_pow_smul_of_countable
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

/-! ### Amenable groups have no free subgroup of rank two -/

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

/-- If `Disjoint ((ρ ^ n) • D) D` for all `n > 0`, then `univ` and `Dᶜ` are equidecomposable. -/
theorem absorb_equidecomposable {G X : Type*} [Group G] [MulAction G X] (ρ : G) (D : Set X)
    (hρ : ∀ n : ℕ, 0 < n → Disjoint ((ρ ^ n) • D) D) :
    Equidecomposable G (Set.univ : Set X) Dᶜ := by
  classical
  set E : Set X := ⋃ n : ℕ, (ρ ^ n) • D with hE
  have hDE : D ⊆ E := fun x hx => Set.mem_iUnion.2 ⟨0, by simpa using hx⟩
  have hρE : ρ • E = ⋃ n : ℕ, (ρ ^ (n + 1)) • D := by
    rw [hE, Set.smul_set_iUnion]
    congr 1; ext n; rw [smul_smul, pow_succ']
  have hρE_sub : ρ • E ⊆ E := by
    rw [hρE]; intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨n + 1, hn⟩
  have hρE_disj : Disjoint (ρ • E) D := by
    rw [hρE, Set.disjoint_iUnion_left]
    intro n; exact hρ (n + 1) (Nat.succ_pos n)
  have hE_split : ∀ y, y ∈ E → y ∉ D → y ∈ ρ • E := by
    intro y hy hyD
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
    cases n with
    | zero => simp at hn; exact absurd hn hyD
    | succ n => rw [hρE]; exact Set.mem_iUnion.2 ⟨n, hn⟩
  let f : PartialEquiv X X :=
    { toFun := fun x => if x ∈ E then ρ • x else x
      invFun := fun y => if y ∈ ρ • E then ρ⁻¹ • y else y
      source := Set.univ
      target := Dᶜ
      map_source' := by
        intro x _
        by_cases hx : x ∈ E
        · simp only [hx, if_true]
          exact fun h => Set.disjoint_left.1 hρE_disj (Set.smul_mem_smul_set hx) h
        · simp only [hx, if_false]
          exact fun h => hx (hDE h)
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := by
        intro x _
        by_cases hx : x ∈ E
        · simp [hx, Set.smul_mem_smul_set hx]
        · have : x ∉ ρ • E := fun h => hx (hρE_sub h)
          simp [hx, this]
      right_inv' := by
        intro y hy
        by_cases hy' : y ∈ ρ • E
        · have : ρ⁻¹ • y ∈ E := Set.mem_smul_set_iff_inv_smul_mem.1 hy'
          simp [hy', this]
        · have : y ∉ E := fun h => hy' (hE_split y h hy)
          simp [hy', this] }
  refine ⟨⟨f, ⟨{ρ, 1}, ?_⟩⟩, rfl, rfl⟩
  intro x _
  by_cases hx : x ∈ E
  · exact ⟨ρ, by simp, by simp [f, hx]⟩
  · exact ⟨1, by simp, by simp [f, hx]⟩

/-! ## Part 1: rotations -/

theorem exists_disjoint_pow_smul_of_countable' (D : Set (Sphere 2)) (hD : D.Countable) :
    ∃ ρ : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ n : ℕ, 0 < n → Disjoint ((ρ ^ n) • D) D :=
  Garrido.exists_disjoint_pow_smul_of_countable D hD

theorem equidecomposable_univ_compl_of_countable' (D : Set (Sphere 2)) (hD : D.Countable) :
    Equidecomposable (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) Dᶜ := by
  obtain ⟨ρ, hρ⟩ := exists_disjoint_pow_smul_of_countable' D hD
  exact absorb_equidecomposable ρ D hρ

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

theorem exists_disjoint_pow_smul_of_countable (D : Set (Sphere 2)) (hD : D.Countable) :
    ∃ ρ : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ n : ℕ, 0 < n → Disjoint ((ρ ^ n) • D) D :=
  Garrido.exists_disjoint_pow_smul_of_countable D hD

theorem equidecomposable_univ_compl_of_countable (D : Set (Sphere 2)) (hD : D.Countable) :
    Equidecomposable (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) Dᶜ :=
  Garrido.BT.equidecomposable_univ_compl_of_countable' D hD

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution (D : Set (Sphere 2)) (hD : D.Countable) :
    Equidecomposable (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) Dᶜ :=
  Garrido.BT.Final.equidecomposable_univ_compl_of_countable D hD
