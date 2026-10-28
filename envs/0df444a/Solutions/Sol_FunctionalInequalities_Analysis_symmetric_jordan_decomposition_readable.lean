-- Prove2me | solution 1 for FunctionalInequalities.Analysis.symmetric_jordan_decomposition_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:16.910696+00:00
-- url     : https://prove2.me/submissions/fa5ff08a-3214-4fb7-971f-c81b09134fcc

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign
import Theorems.Thm_FunctionalInequalities_Analysis_cfc_eq_mul_diagonal_mul_readable

section
open Matrix
section JordanTrace
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Positivity of a real diagonal matrix, proved by an explicit Gram factor. -/
private theorem FunctionalInequalities.Analysis.diagonal_posSemidef (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (Matrix.diagonal d).PosSemidef := by
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i => Real.sqrt (d i))
  have he : D.conjTranspose * D = Matrix.diagonal d := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [D, Matrix.mul_apply, Matrix.diagonal_apply, pow_two] using
        Real.sq_sqrt (hd i)
    · simp [D, Matrix.mul_apply, Matrix.diagonal_apply, hij]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self D
/-- Positivity of a nonnegative real spectral function, using the actual
orthonormal spectral representation of the matrix CFC. -/
theorem FunctionalInequalities.Analysis.cfc_posSemidef_of_nonneg (B : Matrix ι ι ℝ) (hB : B.IsSymm)
    (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) : (cfc f B).PosSemidef := by
  have hHerm : B.IsHermitian := by
    change B.conjTranspose = B
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hB.eq]
  rw [FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul_readable hHerm f]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (diagonal_posSemidef (fun i => f (hHerm.eigenvalues i))
      (fun i => hf (hHerm.eigenvalues i))).mul_mul_conjTranspose_same
        (hHerm.eigenvectorUnitary : Matrix ι ι ℝ)
end JordanTrace
end

noncomputable section
open scoped MatrixOrder
section Jordan
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma FunctionalInequalities.Analysis.scalar_jordan_identities (x : ℝ) :
    max x 0 - max (-x) 0 = x ∧ max x 0 * max (-x) 0 = 0 := by
  by_cases hx : 0 ≤ x
  · have hn : -x ≤ 0 := neg_nonpos.mpr hx
    simp [max_eq_left hx, max_eq_right hn]
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hn : 0 ≤ -x := neg_nonneg.mpr hx'
    simp [max_eq_right hx', max_eq_left hn]
/-- The positive and negative parts are constructed by the matrix CFC.
No Jordan identities or decomposition witnesses are hypotheses. This also
includes the empty index type. -/
theorem solution (B : Matrix ι ι ℝ) (hB : B.IsSymm) :
    ∃ P N : Matrix ι ι ℝ,
      P.PosSemidef ∧ N.PosSemidef ∧ B = P - N ∧
      P * N = 0 ∧ N * P = 0 ∧
      (B * B).trace = (P * P).trace + (N * N).trace := by
  let P : Matrix ι ι ℝ := cfc (fun x : ℝ => max x 0) B
  let N : Matrix ι ι ℝ := cfc (fun x : ℝ => max (-x) 0) B
  have hP : P.PosSemidef :=
    FunctionalInequalities.Analysis.cfc_posSemidef_of_nonneg B hB (fun x : ℝ => max x 0)
      (fun x => le_max_right x 0)
  have hN : N.PosSemidef :=
    FunctionalInequalities.Analysis.cfc_posSemidef_of_nonneg B hB (fun x : ℝ => max (-x) 0)
      (fun x => le_max_right (-x) 0)
  have hspec : (spectrum ℝ B).Finite := Matrix.finite_real_spectrum (A := B)
  have hmul (f g : ℝ → ℝ) :
      cfc f B * cfc g B = cfc (fun x => f x * g x) B := by
    rw [← cfc_mul (hf := hspec.continuousOn f) (hg := hspec.continuousOn g)]
  have hdec : B = P - N := by
    calc
      B = cfc (fun x : ℝ => x) B := (cfc_id ℝ B hB).symm
      _ = cfc (fun x : ℝ => max x 0 - max (-x) 0) B := by
        apply cfc_congr
        intro x hx
        exact (FunctionalInequalities.Analysis.scalar_jordan_identities x).1.symm
      _ = P - N := by
        dsimp [P, N]
        rw [cfc_sub
          (hf := hspec.continuousOn (fun x : ℝ => max x 0))
          (hg := hspec.continuousOn (fun x : ℝ => max (-x) 0))]
  have hPN : P * N = 0 := by
    change cfc (fun x : ℝ => max x 0) B *
      cfc (fun x : ℝ => max (-x) 0) B = 0
    rw [hmul]
    calc
      cfc (fun x : ℝ => max x 0 * max (-x) 0) B =
          cfc (fun _ : ℝ => 0) B := by
        apply cfc_congr
        intro x hx
        exact (FunctionalInequalities.Analysis.scalar_jordan_identities x).2
      _ = 0 := by simp
  have hNP : N * P = 0 := by
    change cfc (fun x : ℝ => max (-x) 0) B *
      cfc (fun x : ℝ => max x 0) B = 0
    rw [hmul]
    calc
      cfc (fun x : ℝ => max (-x) 0 * max x 0) B =
          cfc (fun _ : ℝ => 0) B := by
        apply cfc_congr
        intro x hx
        exact (mul_comm (max (-x) 0) (max x 0)).trans
          (FunctionalInequalities.Analysis.scalar_jordan_identities x).2
      _ = 0 := by simp
  have hsq : (P - N) * (P - N) = P * P + N * N := by
    calc
      (P - N) * (P - N) = P * P - P * N - N * P + N * N := by
        noncomm_ring
      _ = P * P + N * N := by rw [hPN, hNP]; simp
  have htrace : (B * B).trace = (P * P).trace + (N * N).trace := by
    rw [hdec, hsq, Matrix.trace_add]
  exact ⟨P, N, hP, hN, hdec, hPN, hNP, htrace⟩
