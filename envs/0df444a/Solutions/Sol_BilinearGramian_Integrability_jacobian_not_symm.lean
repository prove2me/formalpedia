-- Prove2me | solution 1 for BilinearGramian.Integrability.jacobian_not_symm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-18T09:23:00.668766+00:00
-- url     : https://prove2.me/submissions/3bb122c3-d7db-4b16-9324-a1e217794bb4

import Theorems.Thm_BilinearGramian_Integrability_gramian_explicit

open Matrix BilinearGramian.Integrability
open scoped Topology

private theorem gramian_general (ν : ℝ) (y : Fin 2 → ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : IsLinGramian exA (fun _ : Fin 1 => exN ν) exB y P) :
    P = !![(1 + ν * y 1)^2 / 2, (1 + ν * y 1)*(1 + ν * y 0)/3;
           (1 + ν * y 1)*(1 + ν * y 0)/3, (1 + ν * y 0)^2/4] := by
  have entries (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hP
  have h00 := entries 0 0
  have h01 := entries 0 1
  have h10 := entries 1 0
  have h11 := entries 1 1
  norm_num [IsLinGramian, exA, exN, exB, exb, gramRHS, Matrix.mul_apply,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.vecMulVec,
    Matrix.transpose_apply] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num <;> nlinarith

private theorem field_formula (ν : ℝ) (y : Fin 2 → ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : IsLinGramian exA (fun _ : Fin 1 => exN ν) exB y P)
    (ha : 1 + ν * y 1 ≠ 0) (hb : 1 + ν * y 0 ≠ 0) :
    P⁻¹ *ᵥ y = ![18 * (y 0 * ((1 + ν * y 1)⁻¹)^2) -
      24 * (y 1 * (1 + ν * y 1)⁻¹ * (1 + ν * y 0)⁻¹),
      36 * (y 1 * ((1 + ν * y 0)⁻¹)^2) -
      24 * (y 0 * (1 + ν * y 1)⁻¹ * (1 + ν * y 0)⁻¹)] := by
  have hi : P⁻¹ = !![18 / (1 + ν * y 1)^2, -24 / ((1 + ν * y 1)*(1 + ν * y 0));
      -24 / ((1 + ν * y 1)*(1 + ν * y 0)), 36 / (1 + ν * y 0)^2] := by
    apply Matrix.inv_eq_right_inv
    rw [gramian_general ν y P hP]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  rw [hi]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring

theorem solution (ν ξ : ℝ) (hνξ0 : ν * ξ ≠ 0) (hνξ : 1 + ν * ξ ≠ 0)
    (Pt : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hPt : ∀ x, IsLinGramian exA (fun _ : Fin 1 => exN ν) exB x (Pt x)) :
    HasFDerivAt (fun y => (Pt y)⁻¹ *ᵥ y)
        (Matrix.toLin' ((Pt (ξ • ![1, 1]))⁻¹ +
          (12 * ν * ξ / (1 + ν * ξ) ^ 3) • !![2, -1; -4, 2])).toContinuousLinearMap
        (ξ • ![1, 1]) ∧
      ¬ ((Pt (ξ • ![1, 1]))⁻¹ + (12 * ν * ξ / (1 + ν * ξ) ^ 3) • !![2, -1; -4, 2]).IsSymm := by
  have hi := (gramian_explicit ν ξ hνξ (Pt (ξ • ![1, 1])) (hPt _)).2
  constructor
  · let x : Fin 2 → ℝ := ξ • ![1, 1]
    have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
    have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
    have hA := (h1.const_mul ν).const_add 1
    have hB := (h0.const_mul ν).const_add 1
    have ha : 1 + ν * x 1 ≠ 0 := by simpa [x] using hνξ
    have hb : 1 + ν * x 0 ≠ 0 := by simpa [x] using hνξ
    have hia := (hasFDerivAt_inv ha).comp x hA
    have hib := (hasFDerivAt_inv hb).comp x hB
    have hd0 := ((h0.mul (hia.pow 2)).const_mul 18).sub
      (((h1.mul hia).mul hib).const_mul 24)
    have hd1 := ((h1.mul (hib.pow 2)).const_mul 36).sub
      (((h0.mul hia).mul hib).const_mul 24)
    have heq : (fun y => (Pt y)⁻¹ *ᵥ y) =ᶠ[𝓝 x]
        (fun y => ![18 * (y 0 * ((1 + ν * y 1)⁻¹)^2) -
          24 * (y 1 * (1 + ν * y 1)⁻¹ * (1 + ν * y 0)⁻¹),
          36 * (y 1 * ((1 + ν * y 0)⁻¹)^2) -
          24 * (y 0 * (1 + ν * y 1)⁻¹ * (1 + ν * y 0)⁻¹)]) := by
      filter_upwards [hA.continuousAt.eventually_ne ha,
        hB.continuousAt.eventually_ne hb] with y hyA hyB
      exact field_formula ν y (Pt y) (hPt y) hyA hyB
    apply HasFDerivAt.congr_of_eventuallyEq _ heq
    apply hasFDerivAt_pi'.mpr
    intro i
    fin_cases i
    · convert hd0 using 1 <;> ext v <;> simp only [hi] <;>
      simp [x, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_two,
        ContinuousLinearMap.toSpanSingleton_apply]
      field_simp
      ring
    · convert hd1 using 1 <;> ext v <;> simp only [hi] <;>
      simp [x, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_two,
        ContinuousLinearMap.toSpanSingleton_apply]
      field_simp
      ring
  · intro hs
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hs
    rw [hi] at he
    norm_num [Matrix.IsSymm, Matrix.transpose_apply] at he
    field_simp at he
    exact hνξ0 (by nlinarith)

#print axioms solution
