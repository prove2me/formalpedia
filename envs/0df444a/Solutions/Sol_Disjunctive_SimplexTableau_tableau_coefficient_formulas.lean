-- Prove2me | solution 1 for Disjunctive.SimplexTableau.tableau_coefficient_formulas
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:53:28.872858+00:00
-- url     : https://prove2.me/submissions/fcbf2d2e-6351-4ed8-aa4f-c55351b1362d

import Mathlib
import Definitions.Def_Disjunctive_SimplexTableau_Tableau

set_option autoImplicit false

open Disjunctive.SimplexTableau in
theorem solution {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (hι_inj : Function.Injective ι)
    (hnonsing : IsUnit (Ahat Atil ι).det) (i : M) (x : Fin n → ℝ) :
    SurplusM Atil btil i x =
      Abar0Row Atil btil ι i - ∑ l, AbarRow Atil ι i l * SurplusM Atil btil (ι l) x := by
  set A := Ahat Atil ι with hA
  have hs : ∀ l, SurplusM Atil btil (ι l) x = (A.mulVec x - Bhat btil ι) l := by
    intro l
    rfl
  have hv : A⁻¹.mulVec (A.mulVec x - Bhat btil ι) = x - A⁻¹.mulVec (Bhat btil ι) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hnonsing,
      Matrix.one_mulVec]
  have key : ∑ l, AbarRow Atil ι i l * SurplusM Atil btil (ι l) x
      = -(dotProduct (Atil i) (A⁻¹.mulVec (A.mulVec x - Bhat btil ι))) := by
    simp only [hs]
    generalize A.mulVec x - Bhat btil ι = s
    simp only [AbarRow, dotProduct, Matrix.mulVec, neg_mul, Finset.sum_neg_distrib,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [key, hv, Abar0Row, SurplusM, dotProduct_sub]
  ring
