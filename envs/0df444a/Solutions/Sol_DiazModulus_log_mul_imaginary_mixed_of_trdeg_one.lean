-- Prove2me | solution 1 for DiazModulus.log_mul_imaginary_mixed_of_trdeg_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T08:58:33.577106+00:00
-- url     : https://prove2.me/submissions/15815e87-99df-4900-81a6-e6526767448a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one

open Complex ComplexConjugate

namespace R2_log_mul_imaginary_mixed_of_trdeg_one

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- The conjugate of a logarithm of an algebraic number is one too. -/
theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact hw.algHom cjQ

/-- So is `-w̄`: its exponential is the inverse of `conj (exp w)`. -/
theorem exp_neg_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (-conj w)) := by
  rw [Complex.exp_neg]; exact (exp_conj_alg hw).inv

/-- Real and imaginary parts of `a z + b z̄ = 0`. -/
theorem re_im_of_comb {a b : ℚ} {z : ℂ} (h : (a : ℂ) * z + (b : ℂ) * conj z = 0) :
    ((a : ℝ) + b) * z.re = 0 ∧ ((a : ℝ) - b) * z.im = 0 := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
    Complex.ratCast_im, Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.zero_im] at hr hi
  exact ⟨by linear_combination hr, by linear_combination hi⟩

/-- Rationals `a, b` not both zero have `a + b ≠ 0` or `a - b ≠ 0`. -/
theorem add_or_sub_ne {a b : ℚ} (hab : ¬(a = 0 ∧ b = 0)) :
    (a : ℝ) + b ≠ 0 ∨ (a : ℝ) - b ≠ 0 := by
  by_cases hs : (a : ℝ) + b = 0
  · refine Or.inr fun hd => hab ⟨?_, ?_⟩
    · exact_mod_cast (by linarith : (a : ℝ) = 0)
    · exact_mod_cast (by linarith : (b : ℝ) = 0)
  · exact Or.inl hs

end R2_log_mul_imaginary_mixed_of_trdeg_one

open R2_log_mul_imaginary_mixed_of_trdeg_one in
theorem solution (l m : ℂ) (hl : l ≠ 0) (hm : m ≠ 0)
    (hel : IsAlgebraic ℚ (Complex.exp l)) (hem : IsAlgebraic ℚ (Complex.exp m))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l, m, conj l, conj m} : Set ℂ)) ≤ 1)
    (himag : (l * m).re = 0) :
    (l.im = 0 ∧ m.re = 0) ∨ (l.re = 0 ∧ m.im = 0) := by
  -- the matrix `[[l, l̄], [-m̄, m]]`: its determinant `l m + l̄ m̄ = 2 Re(l m)` vanishes
  have hdet : l * m = conj l * -conj m := by
    rw [Complex.mul_re] at himag
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
      linear_combination 2 * himag
    · simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
      ring
  -- `-m̄` lies in `ℚ[l, m, l̄, m̄]`, so the new algebra is a subalgebra of the old one
  have hle : Algebra.adjoin ℚ ({l, conj l, -conj m, m} : Set ℂ)
      ≤ Algebra.adjoin ℚ ({l, m, conj l, conj m} : Set ℂ) := by
    refine Algebra.adjoin_le ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Algebra.subset_adjoin (by simp)
    · exact Algebra.subset_adjoin (by simp)
    · exact Subalgebra.neg_mem _ (Algebra.subset_adjoin (by simp))
    · exact Algebra.subset_adjoin (by simp)
  have htr' := (trdeg_le_of_injective (Subalgebra.inclusion hle)
    (Subalgebra.inclusion_injective hle)).trans htr
  have hcm : -conj m ≠ 0 := neg_ne_zero.2 ((map_ne_zero _).2 hm)
  rcases DiazModulus.four_exponentials_trdeg_one l (conj l) (-conj m) m hel (exp_conj_alg hel)
      (exp_neg_conj_alg hem) hem hl ((map_ne_zero _).2 hl) hcm hm hdet htr' with
    ⟨a, b, hab, h1, h2⟩ | ⟨a, b, hab, h1, h2⟩
  · -- dependent rows: `a l - b m̄ = 0` and `a l̄ + b m = 0`; conjugating the first, `2 b m = 0`
    exfalso
    have h1c := congrArg conj h1
    simp only [map_add, map_mul, map_neg, Complex.conj_conj, map_ratCast, map_zero] at h1c
    have hbm : (b : ℂ) * m = 0 := by linear_combination (h2 - h1c) / 2
    have hb : b = 0 := by exact_mod_cast (mul_eq_zero.1 hbm).resolve_right hm
    subst hb
    have ha : a ≠ 0 := fun ha => hab ⟨ha, rfl⟩
    simp only [Rat.cast_zero, zero_mul, add_zero, mul_eq_zero, Rat.cast_eq_zero] at h1
    tauto
  · -- dependent columns: `a l + b l̄ = 0` and `b m - a m̄ = 0`
    obtain ⟨hl1, hl2⟩ := re_im_of_comb h1
    obtain ⟨hm1, hm2⟩ := re_im_of_comb (a := b) (b := -a) (z := m)
      (by push_cast; linear_combination h2)
    push_cast at hm1 hm2
    rcases add_or_sub_ne hab with hs | hd
    · -- `a + b ≠ 0`: `l` is purely imaginary and `m` is real
      refine Or.inr ⟨?_, ?_⟩
      · exact (mul_eq_zero.1 hl1).resolve_left hs
      · exact (mul_eq_zero.1 hm2).resolve_left (fun h => hs (by linarith))
    · -- `a - b ≠ 0`: `l` is real and `m` is purely imaginary
      refine Or.inl ⟨?_, ?_⟩
      · exact (mul_eq_zero.1 hl2).resolve_left hd
      · exact (mul_eq_zero.1 hm1).resolve_left (fun h => hd (by linarith))

#print axioms solution
