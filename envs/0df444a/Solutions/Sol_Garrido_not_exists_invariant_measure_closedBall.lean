-- Prove2me | solution 1 for Garrido.not_exists_invariant_measure_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:12:56.448257+00:00
-- url     : https://prove2.me/submissions/5317783f-29b0-4ecd-8f79-8b7bae95e0ca

import Mathlib
import Theorems.Thm_Garrido_isParadoxical_closedBall_and_isParadoxical_univ
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

/-- `W c`: the elements whose reduced word starts with the letter `c`. -/
def W (c : α × Bool) : Set (FreeGroup α) := {w | (FreeGroup.toWord w).head? = some c}

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

theorem measure_image {G X : Type*} [Group G] [MulAction G X] {m : Set X → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) (hinv : IsInvariant G m) (e : Equidecomp X G) :
    ∀ (W : Finset G) (S : Set X), S ⊆ e.source → Equidecomp.IsDecompOn e S W →
      m S = m (e '' S) := by
  classical
  intro W
  induction W using Finset.induction_on with
  | empty =>
    intro S _ hd
    have : S = ∅ := by
      ext a; simp only [mem_empty_iff_false, iff_false]
      intro ha; obtain ⟨g, hg, -⟩ := hd a ha; simp at hg
    subst this; simp
  | insert w W _ ih =>
    intro S hS hd
    let P := {a ∈ S | e a = w • a}
    let Q := S \ P
    have hPS : P ⊆ S := sep_subset _ _
    have hSPQ : S = P ∪ Q := (union_sdiff_cancel hPS).symm
    have hQ : Equidecomp.IsDecompOn e Q W := by
      intro a ha
      obtain ⟨g, hg, hga⟩ := hd a ha.1
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact absurd ⟨ha.1, hga⟩ ha.2
      · exact ⟨g, hg, hga⟩
    have hmQ := ih Q (sdiff_subset.trans hS) hQ
    have hPimg : e '' P = w • P := by
      rw [← Set.image_smul]
      exact Set.image_congr (fun a ha => ha.2)
    have hdisj : Disjoint (e '' P) (e '' Q) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have : b = a := e.toPartialEquiv.injOn (hS hb.1) (hS ha.1) hab
      exact hb.2 (this ▸ ha)
    rw [hSPQ, image_union, hm.2 _ _ disjoint_sdiff_right, hm.2 _ _ hdisj, hmQ, hPimg,
      hinv]

theorem measure_eq {G X : Type*} [Group G] [MulAction G X] {m : Set X → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) (hinv : IsInvariant G m) {A B : Set X}
    (h : Equidecomposable G A B) : m A = m B := by
  obtain ⟨e, rfl, rfl⟩ := h
  rw [measure_image hm hinv e e.witness _ subset_rfl e.isDecompOn]
  exact congrArg m e.toPartialEquiv.image_source_eq_target

theorem measure_mono {X : Type*} {m : Set X → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) {s t : Set X} (h : s ⊆ t) : m s ≤ m t := by
  rw [← union_sdiff_cancel h, hm.2 _ _ disjoint_sdiff_right]
  exact le_self_add

end Garrido.BT


/-! ## Composition: every milestone, with no hypotheses -/

namespace Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem not_exists_invariant_measure_closedBall :
    ¬ ∃ m : Set (EuclideanSpace ℝ (Fin 3)) → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧
      IsInvariant (EuclideanGroup 3) m ∧
      m (Metric.closedBall 0 1) ≠ 0 ∧ m (Metric.closedBall 0 1) ≠ ⊤ :=
  by
  rintro ⟨m, hm, hinv, h0, htop⟩
  obtain ⟨A, B, hA, hB, -, -, hAB, hAe, hBe⟩ :=
    (Garrido.isParadoxical_closedBall_and_isParadoxical_univ).1 0 1 one_pos
  have h3 := Garrido.BT.measure_mono hm (Set.union_subset hA hB)
  rw [hm.2 _ _ hAB, Garrido.BT.measure_eq hm hinv hAe, Garrido.BT.measure_eq hm hinv hBe] at h3
  have : m (Metric.closedBall 0 1) + m (Metric.closedBall 0 1) ≤
      m (Metric.closedBall 0 1) + 0 := by rwa [add_zero]
  exact h0 (le_antisymm (ENNReal.le_of_add_le_add_left htop this) bot_le)

theorem isParadoxical_closedBall_and_isParadoxical_univ :
    (∀ (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
        IsParadoxical (EuclideanGroup 3) (Metric.closedBall c r)) ∧
      IsParadoxical (EuclideanGroup 3) (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) :=
  Garrido.isParadoxical_closedBall_and_isParadoxical_univ

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution :
    ¬ ∃ m : Set (EuclideanSpace ℝ (Fin 3)) → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧
      IsInvariant (EuclideanGroup 3) m ∧
      m (Metric.closedBall 0 1) ≠ 0 ∧ m (Metric.closedBall 0 1) ≠ ⊤ :=
  Garrido.BT.Final.not_exists_invariant_measure_closedBall
