-- Prove2me | solution 1 for DiazModulus.log_mul_real_trichotomy_of_trdeg_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T08:58:36.28608+00:00
-- url     : https://prove2.me/submissions/76d19886-2b48-42bb-a24d-2e7343f303e4

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one

open Complex ComplexConjugate

namespace R2_log_mul_real_trichotomy_of_trdeg_one

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- The conjugate of a logarithm of an algebraic number is one too. -/
theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact hw.algHom cjQ

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

end R2_log_mul_real_trichotomy_of_trdeg_one

open R2_log_mul_real_trichotomy_of_trdeg_one in
theorem solution (l m : ℂ) (hl : l ≠ 0) (hm : m ≠ 0)
    (hel : IsAlgebraic ℚ (Complex.exp l)) (hem : IsAlgebraic ℚ (Complex.exp m))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l, m, conj l, conj m} : Set ℂ)) ≤ 1)
    (hreal : (l * m).im = 0) :
    (l.im = 0 ∧ m.im = 0) ∨ (l.re = 0 ∧ m.re = 0) ∨ ∃ q : ℚ, m = (q : ℂ) * conj l := by
  -- the matrix `[[l, l̄], [m̄, m]]`: its determinant `l m - l̄ m̄ = 2i Im(l m)` vanishes
  have hdet : l * m = conj l * conj m := by
    rw [← map_mul]; exact (Complex.conj_eq_iff_im.2 hreal).symm
  have hset : ({l, conj l, conj m, m} : Set ℂ) = {l, m, conj l, conj m} := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rcases DiazModulus.four_exponentials_trdeg_one l (conj l) (conj m) m hel (exp_conj_alg hel)
      (exp_conj_alg hem) hem hl ((map_ne_zero _).2 hl) ((map_ne_zero _).2 hm) hm hdet
      (hset ▸ htr) with ⟨a, b, hab, h1, h2⟩ | ⟨a, b, hab, h1, h2⟩
  · -- dependent rows: `a l + b m̄ = 0` and `a l̄ + b m = 0`, so `b ≠ 0` and `m = (-a/b) l̄`
    have hb : b ≠ 0 := by
      rintro rfl
      have ha : a ≠ 0 := fun ha => hab ⟨ha, rfl⟩
      simp only [Rat.cast_zero, zero_mul, add_zero, mul_eq_zero, Rat.cast_eq_zero] at h1
      tauto
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
    refine Or.inr (Or.inr ⟨-a / b, ?_⟩)
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hbC]
    linear_combination h2
  · -- dependent columns: `a l + b l̄ = 0` and `b m + a m̄ = 0`
    obtain ⟨hl1, hl2⟩ := re_im_of_comb h1
    obtain ⟨hm1, hm2⟩ := re_im_of_comb (a := b) (b := a) (z := m) (by linear_combination h2)
    rcases add_or_sub_ne hab with hs | hd
    · -- `a + b ≠ 0`: both are purely imaginary
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · exact (mul_eq_zero.1 hl1).resolve_left hs
      · exact (mul_eq_zero.1 hm1).resolve_left (by rwa [add_comm])
    · -- `a - b ≠ 0`: both are real
      refine Or.inl ⟨?_, ?_⟩
      · exact (mul_eq_zero.1 hl2).resolve_left hd
      · exact (mul_eq_zero.1 hm2).resolve_left (fun h => hd (by linarith))

#print axioms solution
