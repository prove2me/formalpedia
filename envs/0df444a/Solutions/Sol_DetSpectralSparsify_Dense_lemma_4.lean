-- Prove2me | solution 1 for DetSpectralSparsify.Dense.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T22:10:41.740248+00:00
-- url     : https://prove2.me/submissions/d8f14840-05ad-4e84-a25d-c2238b73be99

import Definitions.Def_DetSpectralSparsify_Dense_Multigraph

set_option autoImplicit false

open Matrix

theorem chord_scalar (θ l : ℝ) (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    Real.exp (θ * l) ≤ 1 + (Real.exp θ - 1) * l := by
  have := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ θ)
    (show 0 ≤ 1 - l by linarith) h0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
  rw [mul_comm θ l]
  linarith

theorem solution {r : ℕ} (X : Matrix (Fin r) (Fin r) ℝ) (hX0 : X.PosSemidef)
    (hX1 : DetSpectralSparsify.Dense.PSDLe X 1) (θ : ℝ) :
    DetSpectralSparsify.Dense.PSDLe (NormedSpace.exp (θ • X)) (1 + (Real.exp θ - 1) • X) := by
  have hH := hX0.isHermitian
  set U : Matrix (Fin r) (Fin r) ℝ := (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hst : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  set l := hH.eigenvalues with hl
  have hX : X = U * diagonal l * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hU] using this
  have hunit : IsUnit U := ⟨⟨U, star U, hUU', hUU⟩, rfl⟩
  have hinv : U⁻¹ = star U := Matrix.inv_eq_right_inv hUU'
  have hD : θ • diagonal l = diagonal (fun i => θ * l i) := by
    ext i j; simp [diagonal_apply]
  have hexp : NormedSpace.exp (θ • X) = U * diagonal (fun i => Real.exp (θ * l i)) * star U := by
    have h1 : θ • X = U * diagonal (fun i => θ * l i) * U⁻¹ := by
      rw [hinv, ← hD, hX]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, Matrix.exp_conj _ _ hunit, hinv, Matrix.exp_diagonal]
    congr 2
    ext i j
    simp [diagonal_apply, Real.exp_eq_exp_ℝ]
  have hl0 : ∀ i, 0 ≤ l i := fun i => hX0.eigenvalues_nonneg i
  have hl1 : ∀ i, l i ≤ 1 := by
    have h : (star U * (1 - X) * U).PosSemidef := by
      have := hX1.conjTranspose_mul_mul_same U
      simpa [hst] using this
    have e : star U * (1 - X) * U = diagonal (fun i => 1 - l i) := by
      rw [hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
      have : star U * (U * diagonal l * star U) * U = diagonal l := by
        calc star U * (U * diagonal l * star U) * U
            = (star U * U) * diagonal l * (star U * U) := by simp only [Matrix.mul_assoc]
          _ = diagonal l := by rw [hUU]; simp
      rw [this]
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h, Matrix.one_apply]
    rw [e, posSemidef_diagonal_iff] at h
    intro i; have := h i; simp at this; linarith
  have key : (1 + (Real.exp θ - 1) • X) - NormedSpace.exp (θ • X) =
      U * diagonal (fun i => 1 + (Real.exp θ - 1) * l i - Real.exp (θ * l i)) * star U := by
    have hg : diagonal (fun i => 1 + (Real.exp θ - 1) * l i - Real.exp (θ * l i)) =
        1 + (Real.exp θ - 1) • diagonal l - diagonal (fun i => Real.exp (θ * l i)) := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
    rw [hexp, hg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      hUU', Matrix.mul_smul, Matrix.smul_mul, ← hX]
  unfold DetSpectralSparsify.Dense.PSDLe
  rw [key]
  have hd : (diagonal (fun i => 1 + (Real.exp θ - 1) * l i - Real.exp (θ * l i))).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro i
    have := chord_scalar θ (l i) (hl0 i) (hl1 i)
    linarith
  have := hd.mul_mul_conjTranspose_same U
  simpa [hst] using this
