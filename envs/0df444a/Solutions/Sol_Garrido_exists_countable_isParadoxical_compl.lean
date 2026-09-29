-- Prove2me | solution 1 for Garrido.exists_countable_isParadoxical_compl
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:12:51.797871+00:00
-- url     : https://prove2.me/submissions/7e922336-aa74-4cad-8b89-5c8da16b5128

import Mathlib
import Theorems.Thm_Garrido_isParadoxical_freeGroup_and_isParadoxical_of_actsFreely
import Theorems.Thm_Garrido_exists_injective_freeGroup_specialOrthogonalGroup
import Theorems.Thm_Garrido_exists_fixedPoints_eq_pair_of_ne_one
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

/-- Garrido Proposition 1.5. -/
theorem isParadoxical_freeGroup_and_isParadoxical_of_actsFreely' :
    IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set (FreeGroup (Fin 2))) ∧
      ∀ (X : Type u) [MulAction (FreeGroup (Fin 2)) X] [Nonempty X],
        ActsFreely (FreeGroup (Fin 2)) X → IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set X) :=
  Garrido.isParadoxical_freeGroup_and_isParadoxical_of_actsFreely

/-! ### Amenable groups have no free subgroup of rank two -/

end Garrido.BT


namespace Garrido.BT

open Matrix
theorem exists_injective_freeGroup_specialOrthogonalGroup' :
    ∃ f : FreeGroup (Fin 2) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      Function.Injective f :=
  Garrido.exists_injective_freeGroup_specialOrthogonalGroup

end Garrido.BT


namespace Garrido.BT

open Matrix

theorem exists_fixedPoints_eq_pair_of_ne_one' (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hA : A ≠ 1) : ∃ x : Sphere 2, {y : Sphere 2 | A • y = y} = {x, -x} :=
  Garrido.exists_fixedPoints_eq_pair_of_ne_one A hA

/-! ### Transfer of equidecompositions from an invariant subtype -/

section Transfer

open Set

variable {G H Y : Type*} [Group G] [MulAction G Y] [Group H]

open Classical in
/-- Extend a self-map of a subtype by the identity. -/
noncomputable def liftFun (E : Set Y) (g : E → E) : Y → Y :=
  fun y => if h : y ∈ E then (g ⟨y, h⟩ : Y) else y

theorem liftFun_coe (E : Set Y) (g : E → E) (a : E) : liftFun E g a = g a := by
  simp [liftFun]

/-- An equidecomposition of a subtype `E` (acted on by `H` through `φ : H →* G`) gives an
equidecomposition of the images in `Y` under `G`. -/
noncomputable def liftEquidecomp (E : Set Y) [MulAction H E] (φ : H →* G)
    (hφ : ∀ (h : H) (y : E), ((h • y : E) : Y) = φ h • (y : Y)) (e : Equidecomp E H) :
    Equidecomp Y G where
  toFun := liftFun E e
  invFun := liftFun E e.toPartialEquiv.symm
  source := Subtype.val '' e.source
  target := Subtype.val '' e.target
  map_source' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨e a, e.toPartialEquiv.map_source ha, (liftFun_coe _ _ _).symm⟩
  map_target' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨e.toPartialEquiv.symm a, e.toPartialEquiv.map_target ha, (liftFun_coe _ _ _).symm⟩
  left_inv' := by
    rintro _ ⟨a, ha, rfl⟩
    rw [liftFun_coe, liftFun_coe]
    exact congrArg Subtype.val (e.toPartialEquiv.left_inv ha)
  right_inv' := by
    rintro _ ⟨a, ha, rfl⟩
    rw [liftFun_coe, liftFun_coe]
    exact congrArg Subtype.val (e.toPartialEquiv.right_inv ha)
  isDecompOn' := by
    classical
    refine ⟨e.witness.image φ, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg, hga⟩ := e.isDecompOn a ha
    refine ⟨φ g, Finset.mem_image_of_mem _ hg, ?_⟩
    rw [liftFun_coe, hga, hφ]

/-- A paradoxical decomposition of an invariant subtype transfers to the ambient action. -/
theorem isParadoxical_of_subtype (E : Set Y) [MulAction H E] (φ : H →* G)
    (hφ : ∀ (h : H) (y : E), ((h • y : E) : Y) = φ h • (y : Y))
    (hP : IsParadoxical H (Set.univ : Set E)) : IsParadoxical G E := by
  obtain ⟨A, B, -, -, hAne, hBne, hdisj, ⟨eA, hsA, htA⟩, ⟨eB, hsB, htB⟩⟩ := hP
  have hE : Subtype.val '' (Set.univ : Set E) = E := Subtype.coe_image_univ E
  refine ⟨Subtype.val '' A, Subtype.val '' B, Subtype.coe_image_subset _ _,
    Subtype.coe_image_subset _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hAne; apply Subtype.val_injective.image_injective; rw [h, hE]
  · intro h; apply hBne; apply Subtype.val_injective.image_injective; rw [h, hE]
  · exact (Set.disjoint_image_iff Subtype.val_injective).mpr hdisj
  · refine ⟨liftEquidecomp E φ hφ eA, ?_, ?_⟩
    · change Subtype.val '' eA.source = _; rw [hsA]
    · change Subtype.val '' eA.target = _; rw [htA, hE]
  · refine ⟨liftEquidecomp E φ hφ eB, ?_, ?_⟩
    · change Subtype.val '' eB.source = _; rw [hsB]
    · change Subtype.val '' eB.target = _; rw [htB, hE]

end Transfer

/-! ### The sphere is uncountable -/

theorem not_countable_sphere_two : ¬ (Set.univ : Set (Sphere 2)).Countable := by
  intro hc
  have hmem : ∀ t : Set.Icc (0 : ℝ) 1,
      (WithLp.toLp 2 ![(t : ℝ), √(1 - (t : ℝ) ^ 2), 0] : EuclideanSpace ℝ (Fin 3)) ∈ Sphere 2 := by
    intro t
    have h1 : 0 ≤ 1 - (t : ℝ) ^ 2 := by nlinarith [t.2.1, t.2.2]
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp [Real.sq_sqrt h1]
  let g : Set.Icc (0 : ℝ) 1 → Sphere 2 := fun t => ⟨_, hmem t⟩
  have hg : Function.Injective g := by
    intro s t h
    have := congrArg (fun z : Sphere 2 => z.1.ofLp 0) h
    exact Subtype.ext (by simpa [g] using this)
  have : Countable (Sphere 2) := Set.countable_univ_iff.mp hc
  have : Countable (Set.Icc (0 : ℝ) 1) := hg.countable
  have h1 := Cardinal.mk_le_aleph0_iff.mpr (inferInstance : Countable (Set.Icc (0 : ℝ) 1))
  rw [Cardinal.mk_Icc_real zero_lt_one] at h1
  exact absurd Cardinal.aleph0_lt_continuum (not_lt.mpr h1)

/-! ### Theorem 1.7 (Hausdorff) -/

theorem exists_countable_isParadoxical_compl'
    (h_15 : IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set (FreeGroup (Fin 2))) ∧
      ∀ (X : Type) [MulAction (FreeGroup (Fin 2)) X] [Nonempty X],
        ActsFreely (FreeGroup (Fin 2)) X → IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set X))
    (h_16 : ∃ f : FreeGroup (Fin 2) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      Function.Injective f) :
    ∃ D : Set (Sphere 2), D.Countable ∧
      IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) Dᶜ := by
  obtain ⟨f, hf⟩ := h_16
  set D : Set (Sphere 2) := {y | ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ f w • y = y} with hD
  have hfne : ∀ w, w ≠ 1 → f w ≠ 1 := fun w hw h => hw (hf (by rw [h, map_one]))
  have hcount : D.Countable := by
    have : D = ⋃ w : {w : FreeGroup (Fin 2) // w ≠ 1}, {y : Sphere 2 | f w • y = y} := by
      ext y; simp [hD]
    rw [this]
    refine Set.countable_iUnion fun w => ?_
    obtain ⟨x, hx⟩ := exists_fixedPoints_eq_pair_of_ne_one' (f w) (hfne w w.2)
    rw [hx]
    exact (Set.toFinite _).countable
  have hinv : ∀ (w : FreeGroup (Fin 2)) (y : Sphere 2), y ∈ Dᶜ → f w • y ∈ Dᶜ := by
    intro w y hy hwy
    obtain ⟨v, hv, hvy⟩ := hwy
    apply hy
    refine ⟨w⁻¹ * v * w, ?_, ?_⟩
    · intro h; apply hv
      calc v = w * (w⁻¹ * v * w) * w⁻¹ := by group
        _ = 1 := by rw [h]; group
    · rw [map_mul, map_mul, mul_smul, mul_smul, hvy, map_inv, inv_smul_smul]
  letI inst : MulAction (FreeGroup (Fin 2)) ↥Dᶜ :=
    { smul := fun w y => ⟨f w • y.1, hinv w y.1 y.2⟩
      one_smul := fun y => Subtype.ext (by
        change f 1 • y.1 = y.1; rw [map_one, one_smul])
      mul_smul := fun a b y => Subtype.ext (by
        change f (a * b) • y.1 = f a • f b • y.1; rw [map_mul, mul_smul]) }
  have : Nonempty ↥Dᶜ := by
    by_contra hne
    rw [not_nonempty_iff, Set.isEmpty_coe_sort, Set.compl_empty_iff] at hne
    exact not_countable_sphere_two (hne ▸ hcount)
  have hfree : ActsFreely (FreeGroup (Fin 2)) ↥Dᶜ := by
    intro w y hwy
    by_contra hw
    exact y.2 ⟨w, hw, congrArg Subtype.val hwy⟩
  refine ⟨D, hcount, ?_⟩
  exact isParadoxical_of_subtype Dᶜ f (fun _ _ => rfl) (h_15.2 ↥Dᶜ hfree)

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

theorem exists_injective_freeGroup_specialOrthogonalGroup :
    ∃ f : FreeGroup (Fin 2) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ, Function.Injective f :=
  Garrido.exists_injective_freeGroup_specialOrthogonalGroup

theorem exists_fixedPoints_eq_pair_of_ne_one (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hA : A ≠ 1) : ∃ x : Sphere 2, {y : Sphere 2 | A • y = y} = {x, -x} :=
  Garrido.exists_fixedPoints_eq_pair_of_ne_one A hA

theorem exists_countable_isParadoxical_compl :
    ∃ D : Set (Sphere 2), D.Countable ∧
      IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) Dᶜ :=
  Garrido.BT.exists_countable_isParadoxical_compl'
    Garrido.BT.isParadoxical_freeGroup_and_isParadoxical_of_actsFreely'.{0}
    Garrido.BT.exists_injective_freeGroup_specialOrthogonalGroup'

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution :
    ∃ D : Set (Sphere 2), D.Countable ∧
      IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) Dᶜ :=
  Garrido.BT.Final.exists_countable_isParadoxical_compl
