-- Prove2me | solution 1 for Garrido.not_exists_invariant_probability_measure_sphere
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:12:55.329006+00:00
-- url     : https://prove2.me/submissions/d873628b-18d7-4ce6-a4ba-b65e9d361921

import Mathlib
import Theorems.Thm_Garrido_isParadoxical_sphere_two_and_isParadoxical_sphere
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

theorem c5_measure_image {G X : Type*} [Group G] [MulAction G X] {m : Set X → ℝ≥0∞}
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
    let R := S \ P
    have hPS : P ⊆ S := sep_subset _ _
    have hSPR : S = P ∪ R := (union_sdiff_cancel hPS).symm
    have hR : Equidecomp.IsDecompOn e R W := by
      intro a ha
      obtain ⟨g, hg, hga⟩ := hd a ha.1
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact absurd ⟨ha.1, hga⟩ ha.2
      · exact ⟨g, hg, hga⟩
    have hmR := ih R (sdiff_subset.trans hS) hR
    have hPimg : e '' P = w • P := by
      rw [← Set.image_smul]
      exact Set.image_congr (fun a ha => ha.2)
    have hdisj : Disjoint (e '' P) (e '' R) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have : b = a := e.toPartialEquiv.injOn (hS hb.1) (hS ha.1) hab
      exact hb.2 (this ▸ ha)
    rw [hSPR, image_union, hm.2 _ _ disjoint_sdiff_right, hm.2 _ _ hdisj, hmR, hPimg,
      hinv]

theorem c5_measure_eq {G X : Type*} [Group G] [MulAction G X] {m : Set X → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) (hinv : IsInvariant G m) {A B : Set X}
    (h : Equidecomposable G A B) : m A = m B := by
  obtain ⟨e, rfl, rfl⟩ := h
  rw [c5_measure_image hm hinv e e.witness _ subset_rfl e.isDecompOn]
  exact congrArg m e.toPartialEquiv.image_source_eq_target

theorem c5_measure_mono {X : Type*} {m : Set X → ℝ≥0∞}
    (hm : IsFinitelyAdditiveMeasure m) {s t : Set X} (h : s ⊆ t) : m s ≤ m t := by
  rw [← union_sdiff_cancel h, hm.2 _ _ disjoint_sdiff_right]
  exact le_self_add

theorem c5_not_isParadoxical_of_measure_eq_one {G X : Type*} [Group G] [MulAction G X]
    {m : Set X → ℝ≥0∞} (hm : IsFinitelyAdditiveMeasure m) (hinv : IsInvariant G m)
    {E : Set X} (hE : m E = 1) : ¬ IsParadoxical G E := by
  rintro ⟨A, B, hA, hB, -, -, hAB, hAE, hBE⟩
  have h1 := c5_measure_eq hm hinv hAE
  have h2 := c5_measure_eq hm hinv hBE
  have h3 := c5_measure_mono hm (union_subset hA hB)
  rw [hm.2 _ _ hAB, h1, h2, hE] at h3
  norm_num at h3

-- Corollary 1.9 (p. 3), Banach–Tarski for spheres

end Garrido.BT


/-! Garrido, Corollary 1.10 (Banach–Tarski for balls and for ℝ³) and the p. 1 consequence. -/

namespace Garrido.BT
open scoped ENNReal Pointwise
open Set Matrix

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ



/-- rotation by `arccos (3/5)` about the first coordinate axis -/
noncomputable def R : SO3 :=
  ⟨!![1, 0, 0; 0, 3 / 5, -(4 / 5); 0, 4 / 5, 3 / 5], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
    · simp [Matrix.det_fin_three]; norm_num⟩

/-! ## The radial projection -/

/-! ## Absorbing the centre -/

/-! ## The targets -/

end Garrido.BT


/-! ## Composition: every milestone, with no hypotheses -/

namespace Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem isParadoxical_sphere_two_and_isParadoxical_sphere :
    IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) ∧
      ∀ n : ℕ, 2 ≤ n →
        IsParadoxical (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) (Set.univ : Set (Sphere n)) :=
  Garrido.isParadoxical_sphere_two_and_isParadoxical_sphere

theorem not_exists_invariant_probability_measure_sphere (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ m : Set (Sphere n) → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧
      IsInvariant (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) m ∧ m Set.univ = 1 :=
  by
  rintro ⟨m, hm, hinv, h1⟩
  exact Garrido.BT.c5_not_isParadoxical_of_measure_eq_one hm hinv h1
    ((Garrido.isParadoxical_sphere_two_and_isParadoxical_sphere).2 n hn)

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ m : Set (Sphere n) → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧
      IsInvariant (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) m ∧ m Set.univ = 1 :=
  Garrido.BT.Final.not_exists_invariant_probability_measure_sphere n hn
