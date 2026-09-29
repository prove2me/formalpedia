-- Prove2me | solution 1 for DiazModulus.candidate_no_real_algebraic_line
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T19:19:47.334226+00:00
-- url     : https://prove2.me/submissions/02f87c60-27d0-4c05-ab14-a06fa9c7201a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate
open DiazModulus

/-!
Cheap line exclusion for a Diaz candidate (Remark rem:line-cheap).

A real-algebraic affine line meets the circle of algebraic radius `|u|` only in
algebraic points; a candidate is transcendental by Hermite–Lindemann.
-/

open DiazModulus in
theorem solution {u : ℂ} (h : IsCandidate u)
    {A B C : ℂ}
    (hA : IsAlgebraic ℚ A) (hB : IsAlgebraic ℚ B) (hC : IsAlgebraic ℚ C)
    (hAim : A.im = 0) (hBim : B.im = 0) (_hCim : C.im = 0)
    (hne : ¬(A = 0 ∧ B = 0)) :
    A * ((u.re : ℝ) : ℂ) + B * ((u.im : ℝ) : ℂ) ≠ C := by
  intro hline
  obtain ⟨hu, hnorm, hexp⟩ := h
  have hHL : HermiteLindemann := hermite_lindemann_holds
  have I_mem_Qbar : (I : ℂ) ∈ Qbar := by
    rw [mem_Qbar_iff]
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (1 : ℚ),
      Polynomial.X_pow_add_C_ne_zero (by norm_num : (0 : ℕ) < 2) (1 : ℚ), ?_⟩
    simp [Polynomial.aeval_add, Polynomial.aeval_X_pow, I_sq]
  set x : ℂ := ((u.re : ℝ) : ℂ)
  set y : ℂ := ((u.im : ℝ) : ℂ)
  have circle : x ^ 2 + y ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    calc
      x ^ 2 + y ^ 2
          = ((u.re ^ 2 + u.im ^ 2 : ℝ) : ℂ) := by
              simp [x, y, ofReal_pow, ofReal_add]
      _ = (Complex.normSq u : ℂ) := by simp [Complex.normSq_apply, pow_two]
      _ = ((‖u‖ : ℝ) : ℂ) ^ 2 := by rw [Complex.normSq_eq_norm_sq, ofReal_pow]
  have u_eq : u = x + y * I := (Complex.re_add_im u).symm
  have hρ : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar :=
    Subfield.pow_mem _ (mem_Qbar_iff.mpr hnorm) 2
  have hAQ : A ∈ Qbar := mem_Qbar_iff.mpr hA
  have hBQ : B ∈ Qbar := mem_Qbar_iff.mpr hB
  have hCQ : C ∈ Qbar := mem_Qbar_iff.mpr hC
  have hsumsq_ne : A ^ 2 + B ^ 2 ≠ 0 := by
    intro hz
    have hre : (A ^ 2 + B ^ 2).re = 0 := by simp [hz]
    have h1 : (A ^ 2).re = A.re ^ 2 - A.im ^ 2 := by
      simp [pow_two, Complex.mul_re]
    have h2 : (B ^ 2).re = B.re ^ 2 - B.im ^ 2 := by
      simp [pow_two, Complex.mul_re]
    have : A.re ^ 2 + B.re ^ 2 = 0 := by
      simp only [Complex.add_re, h1, h2, hAim, hBim] at hre
      -- hre : A.re^2 - 0^2 + (B.re^2 - 0^2) = 0
      simpa using hre
    have hAre0 : A.re = 0 := by nlinarith
    have hBre0 : B.re = 0 := by nlinarith
    exact hne ⟨Complex.ext (by simpa using hAre0) hAim,
      Complex.ext (by simpa using hBre0) hBim⟩
  have hxQ : x ∈ Qbar := by
    by_cases hA0 : A = 0
    · have hBne : B ≠ 0 := fun hB0 => hne ⟨hA0, hB0⟩
      have hy_eq : y = C / B := by
        have : B * y = C := by simpa [hA0] using hline
        field_simp [hBne]
        linear_combination this
      have hyQ : y ∈ Qbar := by
        rw [hy_eq]; exact Subfield.div_mem _ hCQ hBQ
      have hx2 : x ^ 2 ∈ Qbar := by
        have : x ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 - y ^ 2 := by
          linear_combination circle
        rw [this]
        exact Subfield.sub_mem _ hρ (Subfield.pow_mem _ hyQ 2)
      exact mem_Qbar_iff.mpr
        (IsAlgebraic.of_pow (n := 2) (by norm_num) (mem_Qbar_iff.mp hx2))
    · have hx_eq : x = (C - B * y) / A := by
        field_simp [hA0]
        linear_combination hline
      have hcleared :
          (C - B * y) ^ 2 + A ^ 2 * y ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 * A ^ 2 := by
        have hxsubst :
            ((C - B * y) / A) ^ 2 + y ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
          simpa [hx_eq] using circle
        have hmul :
            ((C - B * y) / A) ^ 2 * A ^ 2 + y ^ 2 * A ^ 2 =
              ((‖u‖ : ℝ) : ℂ) ^ 2 * A ^ 2 := by
          have := congrArg (fun z => z * A ^ 2) hxsubst
          -- this : ((…)^2 + y^2) * A^2 = ρ * A^2
          convert this using 1
          ring
        have hsq : ((C - B * y) / A) ^ 2 * A ^ 2 = (C - B * y) ^ 2 := by
          field_simp [hA0]
        rw [hsq] at hmul
        convert hmul using 1
        ring
      have hy_aeval :
          (A ^ 2 + B ^ 2) * y ^ 2 + (-(2 * C * B)) * y +
            (C ^ 2 - ((‖u‖ : ℝ) : ℂ) ^ 2 * A ^ 2) = 0 := by
        have hexpnd :
            (C - B * y) ^ 2 = C ^ 2 - 2 * C * B * y + B ^ 2 * y ^ 2 := by ring
        have hy_poly :
            (A ^ 2 + B ^ 2) * y ^ 2 - (2 * C * B) * y +
              (C ^ 2 - ((‖u‖ : ℝ) : ℂ) ^ 2 * A ^ 2) = 0 := by
          rw [hexpnd] at hcleared
          linear_combination hcleared
        linear_combination hy_poly
      set α : ℂ := A ^ 2 + B ^ 2
      set β : ℂ := -(2 * C * B)
      set γ : ℂ := C ^ 2 - ((‖u‖ : ℝ) : ℂ) ^ 2 * A ^ 2
      have hy0 : α * y ^ 2 + β * y + γ = 0 := by
        simpa [α, β, γ] using hy_aeval
      have hαQ : α ∈ Qbar :=
        Subfield.add_mem _ (Subfield.pow_mem _ hAQ 2) (Subfield.pow_mem _ hBQ 2)
      have hβQ : β ∈ Qbar := by
        change (-(2 * C * B)) ∈ Qbar
        exact Subfield.neg_mem _
          (Subfield.mul_mem _
            (Subfield.mul_mem _ (by simpa using Subfield.natCast_mem Qbar 2) hCQ) hBQ)
      have hγQ : γ ∈ Qbar := by
        change (C ^ 2 - ((‖u‖ : ℝ) : ℂ) ^ 2 * A ^ 2) ∈ Qbar
        exact Subfield.sub_mem _ (Subfield.pow_mem _ hCQ 2)
          (Subfield.mul_mem _ hρ (Subfield.pow_mem _ hAQ 2))
      have hα0 : α ≠ 0 := hsumsq_ne
      -- Completing the square: `(2αy+β)² = β² - 4αγ ∈ Qbar`.
      have hw : (2 * α * y + β) ^ 2 = β ^ 2 - 4 * α * γ := by
        linear_combination (4 * α) * hy0
      have hwQ : ((2 * α * y + β) ^ 2) ∈ Qbar := by
        rw [hw]
        exact Subfield.sub_mem _ (Subfield.pow_mem _ hβQ 2)
          (Subfield.mul_mem _
            (Subfield.mul_mem _ (by simpa using Subfield.natCast_mem Qbar 4) hαQ) hγQ)
      have hwmem : (2 * α * y + β) ∈ Qbar :=
        mem_Qbar_iff.mpr
          (IsAlgebraic.of_pow (n := 2) (by norm_num) (mem_Qbar_iff.mp hwQ))
      have hyQ : y ∈ Qbar := by
        have : y = ((2 * α * y + β) - β) / (2 * α) := by
          field_simp [hα0]
          ring
        rw [this]
        exact Subfield.div_mem _ (Subfield.sub_mem _ hwmem hβQ)
          (Subfield.mul_mem _ (by simpa using Subfield.natCast_mem Qbar 2) hαQ)
      rw [hx_eq]
      exact Subfield.div_mem _
        (Subfield.sub_mem _ hCQ (Subfield.mul_mem _ hBQ hyQ)) hAQ
  have hyQ : y ∈ Qbar := by
    by_cases hA0 : A = 0
    · have hBne : B ≠ 0 := fun hB0 => hne ⟨hA0, hB0⟩
      have hy_eq : y = C / B := by
        have : B * y = C := by simpa [hA0] using hline
        field_simp [hBne]
        linear_combination this
      rw [hy_eq]; exact Subfield.div_mem _ hCQ hBQ
    · have hy2 : y ^ 2 ∈ Qbar := by
        have : y ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 - x ^ 2 := by
          linear_combination circle
        rw [this]
        exact Subfield.sub_mem _ hρ (Subfield.pow_mem _ hxQ 2)
      exact mem_Qbar_iff.mpr
        (IsAlgebraic.of_pow (n := 2) (by norm_num) (mem_Qbar_iff.mp hy2))
  have huQ : u ∈ Qbar := by
    rw [u_eq]
    exact Subfield.add_mem _ hxQ (Subfield.mul_mem _ hyQ I_mem_Qbar)
  exact hHL u hu (mem_Qbar_iff.mp huQ) hexp

