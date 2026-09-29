-- Prove2me | solution 1 for ConvexGeometry.orthant_section_faces_are_coordinate_faces
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-22T15:11:28.889744+00:00
-- url     : https://prove2.me/submissions/ee7a0ae9-a758-47e2-91b0-6555aed36389

import Mathlib

set_option autoImplicit false


/-! From OrthantFace.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- A sufficiently small positive multiple preserves coordinatewise domination. -/
theorem exists_pos_smul_le_of_zero_imp {ι : Type*} [Fintype ι]
    (x y : ι → 𝕜) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hzero : ∀ i, x i = 0 → y i = 0) :
    ∃ a : 𝕜, 0 < a ∧ ∀ i, a * y i ≤ x i := by
  classical
  have hfinite (s : Finset ι) : ∃ a : 𝕜, 0 < a ∧ ∀ i ∈ s, a * y i ≤ x i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a, ha, hbound⟩ := ih
      by_cases hxi : x i = 0
      · refine ⟨a, ha, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          simp [hzero i hxi, hxi]
        · exact hbound j hj
      · obtain ⟨b, hb, hbi⟩ := exists_pos_mul_lt (lt_of_le_of_ne (hx i) (Ne.symm hxi)) (y i)
        refine ⟨min a b, lt_min ha hb, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          calc
            min a b * y i ≤ b * y i := mul_le_mul_of_nonneg_right (min_le_right _ _) (hy i)
            _ ≤ x i := by nlinarith
        · exact (mul_le_mul_of_nonneg_right (min_le_left a b) (hy j)).trans (hbound j hj)
  obtain ⟨a, ha, hab⟩ := hfinite Finset.univ
  exact ⟨a, ha, fun i => hab i (Finset.mem_univ i)⟩

/-- The nonnegative vectors in a linear subspace form a pointed cone. -/
def orthantSection {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) :
    PointedCone 𝕜 (ι → 𝕜) :=
  PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)

theorem mem_orthantSection {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (x : ι → 𝕜) :
    x ∈ orthantSection L ↔ x ∈ L ∧ ∀ i, 0 ≤ x i := Iff.rfl

/-- Every face of an orthant section is closed downward under coordinate support.
This is the substantive domination step in its face/support correspondence. -/
theorem face_mem_of_zero_imp {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) {x y : ι → 𝕜}
    (hx : x ∈ F) (hy : y ∈ orthantSection L)
    (hzero : ∀ i, x i = 0 → y i = 0) : y ∈ F := by
  have hxC := (mem_orthantSection L x).mp (hF.le hx)
  have hyC := (mem_orthantSection L y).mp hy
  obtain ⟨a, ha, hab⟩ := exists_pos_smul_le_of_zero_imp x y hxC.2 hyC.2 hzero
  have hz : x - a • y ∈ orthantSection L := by
    apply (mem_orthantSection L _).mpr
    refine ⟨L.sub_mem hxC.1 (L.smul_mem a hyC.1), ?_⟩
    intro i
    change 0 ≤ x i - a * y i
    exact sub_nonneg.mpr (hab i)
  apply hF.mem_of_smul_add_mem hy hz ha
  simpa using hx

end MagicSquaresGeometry

/-! From OrthantFaceSupport.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Every face has a point that uses every coordinate used anywhere in the face. -/
theorem exists_max_support_point {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) :
    ∃ x : ι → 𝕜, x ∈ F ∧
      ∀ y : ι → 𝕜, y ∈ F → ∀ i, x i = 0 → y i = 0 := by
  classical
  have hchoice (i : ι) : ∃ v : ι → 𝕜, v ∈ F ∧
      (∀ y : ι → 𝕜, y ∈ F → y i ≠ 0 → v i ≠ 0) := by
    by_cases h : ∃ y : ι → 𝕜, y ∈ F ∧ y i ≠ 0
    · obtain ⟨y, hy, hyi⟩ := h
      exact ⟨y, hy, fun _ _ _ => hyi⟩
    · refine ⟨0, F.zero_mem, ?_⟩
      intro y hy hyi
      exact False.elim (h ⟨y, hy, hyi⟩)
  choose v hvF hvcover using hchoice
  let x : ι → 𝕜 := ∑ i : ι, v i
  have hx : x ∈ F := F.sum_mem (fun i _ => hvF i)
  refine ⟨x, hx, ?_⟩
  intro y hy i hxi
  by_contra hyi
  have hvi : v i i ≠ 0 := hvcover i y hy hyi
  have hnonneg (j : ι) : 0 ≤ v j i :=
    ((mem_orthantSection L (v j)).mp (hF.le (hvF j))).2 i
  have hle : v i i ≤ x i := by
    change v i i ≤ (∑ j : ι, v j) i
    rw [Finset.sum_apply]
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hzero : v i i = 0 := le_antisymm (hxi ▸ hle) (hnonneg i)
  exact hvi hzero

/-- Faces of an orthant section are exactly its members with fixed zero coordinates. -/
theorem exists_face_zero_characterization {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) :
    ∃ x : ι → 𝕜, x ∈ F ∧ ∀ y : ι → 𝕜,
      (y ∈ F ↔ y ∈ orthantSection L ∧ ∀ i, x i = 0 → y i = 0) := by
  obtain ⟨x, hx, hmax⟩ := exists_max_support_point L F hF
  refine ⟨x, hx, fun y => ?_⟩
  constructor
  · intro hy
    exact ⟨hF.le hy, hmax y hy⟩
  · rintro ⟨hy, hzero⟩
    exact face_mem_of_zero_imp L F hF hx hy hzero

end MagicSquaresGeometry

/-! From OrthantCoordinateFace.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Impose additional coordinate zeros on an orthant section. -/
def coordinateFace {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (B : Set ι) :
    PointedCone 𝕜 (ι → 𝕜) where
  carrier := {x | x ∈ orthantSection L ∧ ∀ i, i ∉ B → x i = 0}
  zero_mem' := ⟨(orthantSection L).zero_mem, by simp⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨(orthantSection L).add_mem hx.1 hy.1, ?_⟩
    intro i hi
    change x i + y i = 0
    rw [hx.2 i hi, hy.2 i hi, add_zero]
  smul_mem' := by
    intro a x hx
    refine ⟨(orthantSection L).smul_mem a.property hx.1, ?_⟩
    intro i hi
    change (a : 𝕜) * x i = 0
    rw [hx.2 i hi, mul_zero]

theorem mem_coordinateFace {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (B : Set ι)
    (x : ι → 𝕜) :
    x ∈ coordinateFace L B ↔ x ∈ orthantSection L ∧ ∀ i, i ∉ B → x i = 0 := Iff.rfl

/-- Nonnegativity makes every additional zero-coordinate constraint a face. -/
theorem coordinateFace_isFaceOf {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (B : Set ι) :
    (coordinateFace L B).IsFaceOf (orthantSection L) := by
  constructor
  · exact fun _ hx => hx.1
  · intro x y a hx hy ha hsum
    refine ⟨hx, ?_⟩
    intro i hi
    have hxi := ((mem_orthantSection L x).mp hx).2 i
    have hyi := ((mem_orthantSection L y).mp hy).2 i
    have heq := hsum.2 i hi
    change a * x i + y i = 0 at heq
    nlinarith

theorem isFaceOf_iff_coordinateFace {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜)) :
    F.IsFaceOf (orthantSection L) ↔ ∃ B : Set ι, F = coordinateFace L B := by
  constructor
  · intro hF
    obtain ⟨x, hx, hchar⟩ := exists_face_zero_characterization L F hF
    refine ⟨{i | x i ≠ 0}, ?_⟩
    ext y
    rw [mem_coordinateFace, hchar y]
    simp
  · rintro ⟨B, rfl⟩
    exact coordinateFace_isFaceOf L B

end MagicSquaresGeometry


/-! A platform-facing statement using Mathlib types and operations only. -/

theorem solution {𝕜 ι : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜)) :
    F.IsFaceOf (PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)) ↔
      ∃ B : Set ι, ∀ x : ι → 𝕜,
        (x ∈ F ↔
          x ∈ (PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)) ∧
            ∀ i, i ∉ B → x i = 0) := by
  constructor
  · intro hF
    obtain ⟨B, hEq⟩ := (MagicSquaresGeometry.isFaceOf_iff_coordinateFace L F).mp hF
    refine ⟨B, fun x => ?_⟩
    rw [hEq]
    exact MagicSquaresGeometry.mem_coordinateFace L B x
  · rintro ⟨B, hB⟩
    apply (MagicSquaresGeometry.isFaceOf_iff_coordinateFace L F).mpr
    refine ⟨B, ?_⟩
    ext x
    exact (hB x).trans (MagicSquaresGeometry.mem_coordinateFace L B x).symm
