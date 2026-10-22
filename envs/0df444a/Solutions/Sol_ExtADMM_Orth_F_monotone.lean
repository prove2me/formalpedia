-- Prove2me | solution 1 for ExtADMM.Orth.F_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:50:28.367318+00:00
-- url     : https://prove2.me/submissions/885bdd4d-376a-4225-a132-7f5ddf4619b7

import Mathlib
import Definitions.Def_ExtADMM_Orth_Setting
set_option autoImplicit false
open ExtADMM.Orth

theorem ll_tr {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (x : Fin n → ℝ) (l : Fin p → ℝ) :
    dotProduct x (A.transpose.mulVec l) = dotProduct (A.mulVec x) l := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem solution {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (a b : Pt n1 n2 n3 p) :
    0 ≤ pair (a - b) (P.F a - P.F b) := by
  have key : pair (a - b) (P.F a - P.F b) = 0 := by
    have e1 : (P.F a - P.F b).x1 = -(P.A1.transpose.mulVec (a.lam - b.lam)) := by
      show -(P.A1.transpose.mulVec a.lam) - -(P.A1.transpose.mulVec b.lam) = _
      rw [Matrix.mulVec_sub]; abel
    have e2 : (P.F a - P.F b).x2 = -(P.A2.transpose.mulVec (a.lam - b.lam)) := by
      show -(P.A2.transpose.mulVec a.lam) - -(P.A2.transpose.mulVec b.lam) = _
      rw [Matrix.mulVec_sub]; abel
    have e3 : (P.F a - P.F b).x3 = -(P.A3.transpose.mulVec (a.lam - b.lam)) := by
      show -(P.A3.transpose.mulVec a.lam) - -(P.A3.transpose.mulVec b.lam) = _
      rw [Matrix.mulVec_sub]; abel
    have e4 : (P.F a - P.F b).lam = P.A1.mulVec (a.x1 - b.x1) + P.A2.mulVec (a.x2 - b.x2)
        + P.A3.mulVec (a.x3 - b.x3) := by
      show P.residual a.x1 a.x2 a.x3 - P.residual b.x1 b.x2 b.x3 = _
      simp only [Problem.residual, Matrix.mulVec_sub]; abel
    have h1 : (a - b).x1 = a.x1 - b.x1 := rfl
    have h2 : (a - b).x2 = a.x2 - b.x2 := rfl
    have h3 : (a - b).x3 = a.x3 - b.x3 := rfl
    have h4 : (a - b).lam = a.lam - b.lam := rfl
    unfold pair
    rw [e1, e2, e3, e4, h1, h2, h3, h4]
    simp only [dotProduct_neg, ll_tr, dotProduct_add]
    rw [dotProduct_comm (a.lam - b.lam) (P.A1.mulVec _), dotProduct_comm (a.lam - b.lam) (P.A2.mulVec _),
      dotProduct_comm (a.lam - b.lam) (P.A3.mulVec _)]
    ring
  exact key.symm ▸ le_refl 0
