-- Prove2me | solution 1 for CyclotomicTrace.finite_add_inv_rootOfUnity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:28:24.612583+00:00
-- url     : https://prove2.me/submissions/07f6a93a-9de5-4ae5-a26d-b2098fe95cde

import Mathlib


section
section
open MeasureTheory Matrix Filter Topology

namespace CyclotomicTrace

open Polynomial

/-- A complex root of `dickson 1 1 n - 2` (`n > 0`) has absolute value at most `2`. -/
theorem norm_le_two_of_dickson {n : ℕ} (hn : 0 < n) {w : ℂ}
    (hw : (dickson 1 (1 : ℂ) n).eval w = 2) : ‖w‖ ≤ 2 := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (w ^ 2 - 4) two_pos
  set y := (w + δ) / 2 with hydef
  have hy : y * (w - y) = 1 := by rw [hydef]; linear_combination (-1 / 4 : ℂ) * hδ
  have hy0 : y ≠ 0 := by rintro h; rw [h, zero_mul] at hy; exact zero_ne_one hy
  have hwy : w = y + y⁻¹ := by
    have : w - y = y⁻¹ := eq_inv_of_mul_eq_one_right hy
    linear_combination this
  rw [hwy, dickson_one_one_eval_add_inv y y⁻¹ (mul_inv_cancel₀ hy0), inv_pow] at hw
  have ht : y ^ n = 1 := by
    have ht0 : y ^ n ≠ 0 := pow_ne_zero _ hy0
    have h2 : (y ^ n - 1) ^ 2 = 0 := by
      field_simp at hw
      linear_combination hw
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have h1 : ‖y‖ = 1 := Complex.norm_eq_one_of_pow_eq_one ht hn.ne'
  calc ‖w‖ = ‖y + y⁻¹‖ := by rw [hwy]
    _ ≤ ‖y‖ + ‖y⁻¹‖ := norm_add_le _ _
    _ = 2 := by rw [norm_inv, h1]; norm_num

/-- `z + z⁻¹` for a root of unity `z` is a root of `dickson 1 1 n - 2`. -/
theorem aeval_dickson_add_inv {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z ^ n = 1) :
    aeval (z + z⁻¹) (dickson 1 (1 : ℤ) n) = 2 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hz
    exact zero_ne_one hz
  rw [aeval_def, eval₂_eq_eval_map, map_dickson, map_one,
    dickson_one_one_eval_add_inv z z⁻¹ (mul_inv_cancel₀ hz0), inv_pow, hz]
  norm_num

theorem finite_add_inv_rootOfUnity (s : Finset ℝ) :
    {r : ℝ | r ∈ Subring.closure (s : Set ℝ) ∧
      ∃ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ (r : ℂ) = z + z⁻¹}.Finite := by
  classical
  set T := {r : ℝ | r ∈ Subring.closure (s : Set ℝ) ∧
      ∃ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ (r : ℂ) = z + z⁻¹} with hT
  let A : Subalgebra ℚ ℝ := Algebra.adjoin ℚ (s : Set ℝ)
  have hRA : ∀ r ∈ Subring.closure (s : Set ℝ), r ∈ A := fun r hr =>
    (Subring.closure_le (t := A.toSubring)).2 Algebra.subset_adjoin hr
  have : Algebra.FiniteType ℚ A :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset _)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have hfin : Module.Finite ℚ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ m)
  have : NumberField (A ⧸ m) :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ (A ⧸ m)).injective
      to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  let ψ : A →+* A ⧸ m := Ideal.Quotient.mk m
  -- the embedding `A → ℂ`
  let g : A →ₐ[ℤ] ℂ := (Complex.ofRealHom.comp (A.val : A →+* ℝ)).toIntAlgHom
  have hg : Function.Injective g := Complex.ofReal_injective.comp Subtype.val_injective
  have hgx : ∀ x : A, g x = ((x : ℝ) : ℂ) := fun _ => rfl
  -- key facts for elements of `T`
  have key : ∀ r ∈ T, ∃ hr : r ∈ A, IsIntegral ℤ (⟨r, hr⟩ : A) ∧
      ∃ n : ℕ, 0 < n ∧ aeval (⟨r, hr⟩ : A) (dickson 1 (1 : ℤ) n) = 2 := by
    rintro r ⟨hrR, z, ⟨n, hn, hz⟩, hrz⟩
    refine ⟨hRA r hrR, ?_, n, hn, ?_⟩
    · rw [← isIntegral_algHom_iff g hg, hgx]
      show IsIntegral ℤ (r : ℂ)
      rw [hrz]
      refine IsIntegral.add (IsIntegral.of_pow hn ?_) (IsIntegral.of_pow hn ?_)
      · rw [hz]; exact isIntegral_one
      · rw [inv_pow, hz, inv_one]; exact isIntegral_one
    · apply hg
      rw [← aeval_algHom_apply, map_ofNat, hgx]
      show aeval (r : ℂ) _ = 2
      rw [hrz]
      exact aeval_dickson_add_inv hn hz
  let f : ℝ → A ⧸ m := fun r => if h : r ∈ A then ψ ⟨r, h⟩ else 0
  refine Set.Finite.of_finite_image (f := f)
    ((NumberField.Embeddings.finite_of_norm_le (A ⧸ m) ℂ 2).subset ?_) ?_
  · rintro _ ⟨r, hr, rfl⟩
    obtain ⟨hrA, hint, n, hn, hP⟩ := key r hr
    simp only [f, dif_pos hrA]
    refine ⟨IsIntegral.map ψ.toIntAlgHom hint, fun φ => norm_le_two_of_dickson hn ?_⟩
    let h : A →ₐ[ℤ] ℂ := (φ.comp ψ).toIntAlgHom
    have := congrArg h hP
    rw [← aeval_algHom_apply, map_ofNat] at this
    rw [← this, aeval_def, eval₂_eq_eval_map, map_dickson, map_one]
    rfl
  · intro r₁ hr₁ r₂ hr₂ h12
    obtain ⟨h1A, hint1, -⟩ := key r₁ hr₁
    obtain ⟨h2A, hint2, -⟩ := key r₂ hr₂
    simp only [f, dif_pos h1A, dif_pos h2A] at h12
    by_contra hne
    have hmem : (⟨r₁, h1A⟩ - ⟨r₂, h2A⟩ : A) ∈ m := Ideal.Quotient.eq.1 h12
    set d : A := ⟨r₁, h1A⟩ - ⟨r₂, h2A⟩ with hd
    have hd0 : (d : ℝ) ≠ 0 := sub_ne_zero.2 hne
    have halg : IsAlgebraic ℚ (d : ℝ) := by
      have : IsIntegral ℤ d := hint1.sub hint2
      rw [← isIntegral_algHom_iff (A.val.restrictScalars ℤ) Subtype.val_injective] at this
      exact (this.tower_top (A := ℚ)).isAlgebraic
    have hinv := A.inv_mem_of_algebraic halg
    have h1 : d * ⟨(d : ℝ)⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hd0)
    apply hm.ne_top
    rw [Ideal.eq_top_iff_one, ← h1]
    exact m.mul_mem_right _ hmem

end CyclotomicTrace

end
end

section
open CyclotomicTrace

theorem solution (s : Finset ℝ) :
    {r : ℝ | r ∈ Subring.closure (s : Set ℝ) ∧
      ∃ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ (r : ℂ) = z + z⁻¹}.Finite := by
  apply CyclotomicTrace.finite_add_inv_rootOfUnity <;> assumption

end
