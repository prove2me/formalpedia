-- Prove2me | solution 1 for DiazModulus.candidate_im_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T12:50:09.452442+00:00
-- url     : https://prove2.me/submissions/20ae0786-7aed-4f82-9585-98248cfaed9d

import Definitions.Def_DiazModulus

open Complex
open DiazModulus

-- Submission bytes for `/verify` against
-- `DiazModulus.candidate_im_transcendental`. Top-level `theorem solution`.

theorem solution (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    Transcendental ℚ ((u.im : ℝ) : ℂ) := by
  have I_mem_Qbar : (I : ℂ) ∈ Qbar := by
    rw [mem_Qbar_iff]
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (1 : ℚ),
      Polynomial.X_pow_add_C_ne_zero (by norm_num : (0 : ℕ) < 2) (1 : ℚ), ?_⟩
    simp [Polynomial.aeval_add, Polynomial.aeval_X_pow, I_sq]
  have ofReal_re_sq_add_im_sq :
      ((u.re : ℝ) : ℂ) ^ 2 + ((u.im : ℝ) : ℂ) ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    calc
      ((u.re : ℝ) : ℂ) ^ 2 + ((u.im : ℝ) : ℂ) ^ 2
          = ((u.re ^ 2 + u.im ^ 2 : ℝ) : ℂ) := by simp [ofReal_pow, ofReal_add]
      _ = (Complex.normSq u : ℂ) := by simp [Complex.normSq_apply, pow_two]
      _ = ((‖u‖ : ℝ) : ℂ) ^ 2 := by rw [Complex.normSq_eq_norm_sq, ofReal_pow]
  have candidate_re_add_im : u = ((u.re : ℝ) : ℂ) + ((u.im : ℝ) : ℂ) * I :=
    (Complex.re_add_im u).symm
  intro hy
  obtain ⟨hu, hnorm, hexp⟩ := h
  set x : ℂ := ((u.re : ℝ) : ℂ)
  set y : ℂ := ((u.im : ℝ) : ℂ)
  have hyQ : y ∈ Qbar := mem_Qbar_iff.mpr hy
  have hρ : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar :=
    Subfield.pow_mem _ (mem_Qbar_iff.mpr hnorm) 2
  have hx2 : x ^ 2 ∈ Qbar := by
    have : x ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 - y ^ 2 := by
      linear_combination ofReal_re_sq_add_im_sq
    rw [this]
    exact Subfield.sub_mem _ hρ (Subfield.pow_mem _ hyQ 2)
  have hx : IsAlgebraic ℚ x :=
    IsAlgebraic.of_pow (n := 2) (by norm_num) (mem_Qbar_iff.mp hx2)
  have hxQ : x ∈ Qbar := mem_Qbar_iff.mpr hx
  have huQ : u ∈ Qbar := by
    rw [candidate_re_add_im]
    exact Subfield.add_mem _ hxQ (Subfield.mul_mem _ hyQ I_mem_Qbar)
  exact hHL u hu (mem_Qbar_iff.mp huQ) hexp
