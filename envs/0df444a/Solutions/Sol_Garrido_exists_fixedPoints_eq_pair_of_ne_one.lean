-- Prove2me | solution 1 for Garrido.exists_fixedPoints_eq_pair_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T14:07:59.123684+00:00
-- url     : https://prove2.me/submissions/c304c7f7-37a0-4061-a5c6-e11c618dcde5

import Mathlib
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

theorem cross_mulVec_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (v y : Fin 3 → ℝ) :
    (M *ᵥ v) ⨯₃ (M *ᵥ y) = (M.adjugate)ᵀ *ᵥ (v ⨯₃ y) := by
  ext i; fin_cases i <;>
    simp [cross_apply, mulVec, dotProduct, Fin.sum_univ_three, adjugate_fin_three] <;> ring

theorem so3_facts (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    (A : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * A = 1 ∧ (A : Matrix (Fin 3) (Fin 3) ℝ) * (A : Matrix _ _ ℝ)ᵀ = 1
      ∧ (A : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := by
  obtain ⟨h1, h2⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp A.2
  refine ⟨?_, ?_, h2⟩
  · simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp h1
  · simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp h1

theorem mulVec_cross_of_so3 (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (v y : Fin 3 → ℝ) :
    (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (v ⨯₃ y) = (A *ᵥ v) ⨯₃ (A *ᵥ y) := by
  obtain ⟨h1, h2, h3⟩ := so3_facts A
  set M : Matrix (Fin 3) (Fin 3) ℝ := (A : Matrix (Fin 3) (Fin 3) ℝ) with hM
  have hadj : M.adjugate = Mᵀ := by
    calc M.adjugate = M.adjugate * (M * Mᵀ) := by rw [h2, Matrix.mul_one]
      _ = (M.adjugate * M) * Mᵀ := by rw [Matrix.mul_assoc]
      _ = Mᵀ := by rw [adjugate_mul, h3, one_smul, Matrix.one_mul]
  rw [cross_mulVec_mulVec, hadj, transpose_transpose]

theorem det_sub_one_eq_zero (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ((A : Matrix (Fin 3) (Fin 3) ℝ) - 1).det = 0 := by
  obtain ⟨h1, h2, h3⟩ := so3_facts A
  set M : Matrix (Fin 3) (Fin 3) ℝ := (A : Matrix (Fin 3) (Fin 3) ℝ) with hM
  have : M - 1 = M * (1 - M)ᵀ := by
    rw [transpose_sub, transpose_one, Matrix.mul_sub, h2, Matrix.mul_one]
  have h : (M - 1).det = -(M - 1).det := by
    conv_lhs => rw [this, det_mul, det_transpose, h3, one_mul]
    rw [show (1 : Matrix (Fin 3) (Fin 3) ℝ) - M = (-1 : ℝ) • (M - 1) by
      rw [neg_one_smul, neg_sub], det_smul]
    simp; ring
  linarith

/-- Any fixed vector of a nontrivial rotation is a multiple of a given nonzero fixed vector. -/
theorem fixed_eq_smul (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (hA : A ≠ 1)
    {v : Fin 3 → ℝ} (hv0 : v ≠ 0) (hv : (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v)
    {y : Fin 3 → ℝ} (hy : (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ y = y) : ∃ c : ℝ, c • v = y := by
  by_contra hc
  push Not at hc
  have hli : LinearIndependent ℝ ![v, y] := (LinearIndependent.pair_iff' hv0).mpr hc
  have hw : v ⨯₃ y ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hli
  set w := v ⨯₃ y with hwdef
  have hAw : (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w = w := by
    rw [hwdef, mulVec_cross_of_so3, hv, hy]
  set P : Matrix (Fin 3) (Fin 3) ℝ := ![w, v, y] with hP
  have hdet : P.det ≠ 0 := by
    rw [hP, ← triple_product_eq_det, ← hwdef]
    intro h; exact hw (dotProduct_self_eq_zero.mp h)
  set M : Matrix (Fin 3) (Fin 3) ℝ := (A : Matrix (Fin 3) (Fin 3) ℝ) with hM
  have hPM : P * Mᵀ = P := by
    have hrow : ∀ i, M *ᵥ P i = P i := by
      intro i; fin_cases i
      · exact hAw
      · exact hv
      · exact hy
    ext i j
    have := congrFun (hrow i) j
    rw [← this]
    simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  have hMt : Mᵀ = 1 := by
    calc Mᵀ = P⁻¹ * (P * Mᵀ) := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = 1 := by rw [hPM, nonsing_inv_mul _ hu]
  apply hA
  apply Subtype.ext
  change M = 1
  rw [← transpose_transpose M, hMt, transpose_one]

theorem smul_sphere_eq_self_iff (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (y : Sphere 2) :
    A • y = y ↔ (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ y.1.ofLp = y.1.ofLp := by
  constructor
  · intro h
    have := congrArg (fun z : Sphere 2 => z.1.ofLp) h
    exact this
  · intro h
    apply Subtype.ext
    change WithLp.toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ y.1.ofLp) = y.1
    rw [h]

theorem exists_fixedPoints_eq_pair_of_ne_one' (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hA : A ≠ 1) : ∃ x : Sphere 2, {y : Sphere 2 | A • y = y} = {x, -x} := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr (det_sub_one_eq_zero A)
  have hfix : (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hv; exact hv
  set V : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 v with hV
  have hV0 : ‖V‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; intro h; apply hv0
    have := congrArg WithLp.ofLp h; simpa [hV] using this
  have hxmem : ‖V‖⁻¹ • V ∈ Sphere 2 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hV0]
  refine ⟨⟨_, hxmem⟩, ?_⟩
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, smul_sphere_eq_self_iff]
  constructor
  · intro hy
    obtain ⟨c, hc⟩ := fixed_eq_smul A hA hv0 hfix hy
    have hyc : y.1 = c • V := by
      have : WithLp.toLp 2 (y.1.ofLp) = WithLp.toLp 2 (c • v) := by rw [hc]
      simpa [hV] using this
    have hn : |c| * ‖V‖ = 1 := by
      have := mem_sphere_zero_iff_norm.mp y.2
      rw [hyc, norm_smul, Real.norm_eq_abs] at this; exact this
    have habs : |c| = ‖V‖⁻¹ := by field_simp; linarith
    rcases abs_eq (inv_nonneg.mpr (norm_nonneg V)) |>.mp habs with h | h
    · left; apply Subtype.ext; rw [hyc, h]
    · right; apply Subtype.ext; rw [hyc, h, coe_neg_sphere, neg_smul]
  · rintro (rfl | rfl)
    · change (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (‖V‖⁻¹ • v) = ‖V‖⁻¹ • v
      rw [mulVec_smul, hfix]
    · change (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (-(‖V‖⁻¹ • v)) = -(‖V‖⁻¹ • v)
      rw [mulVec_neg, mulVec_smul, hfix]

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

theorem exists_fixedPoints_eq_pair_of_ne_one (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hA : A ≠ 1) : ∃ x : Sphere 2, {y : Sphere 2 | A • y = y} = {x, -x} :=
  Garrido.BT.exists_fixedPoints_eq_pair_of_ne_one' A hA

end Garrido.BT.Final

open Garrido
open scoped ENNReal Pointwise

theorem solution (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hA : A ≠ 1) : ∃ x : Sphere 2, {y : Sphere 2 | A • y = y} = {x, -x} :=
  Garrido.BT.Final.exists_fixedPoints_eq_pair_of_ne_one A hA
