-- Prove2me | solution 1 for Disjunctive.SimplexTableau.reduced_cost_formulas_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:08:32.535453+00:00
-- url     : https://prove2.me/submissions/3658a4f3-b219-41b7-8ecc-c94a6a7b7f34

import Mathlib
import Definitions.Def_Disjunctive_SimplexTableau_Cglp
import Definitions.Def_Disjunctive_SimplexTableau_Tableau
import Definitions.Def_Disjunctive_SimplexTableau_ReducedCost_v2

open Disjunctive.SimplexTableau

namespace RedCostPriv

theorem tableau_id {n : ℕ} {M : Type*} [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M)
    (hnonsing : IsUnit (Ahat Atil ι).det) (i : M) (x : Fin n → ℝ) :
    ∑ j, AbarRow Atil ι i j * SurplusM Atil btil (ι j) x =
      Abar0Row Atil btil ι i - SurplusM Atil btil i x := by
  set A := Ahat Atil ι
  have h1 : ∀ j, AbarRow Atil ι i j = -(Matrix.vecMul (Atil i) A⁻¹) j := by
    intro j; simp [AbarRow, Matrix.vecMul, dotProduct, A]
  have h2 : ∀ j, SurplusM Atil btil (ι j) x = (A.mulVec x - Bhat btil ι) j := by
    intro j; simp [SurplusM, Matrix.mulVec, A, Ahat, Bhat, dotProduct]
  have hsum : ∑ j, AbarRow Atil ι i j * SurplusM Atil btil (ι j) x =
      -(dotProduct (Matrix.vecMul (Atil i) A⁻¹) (A.mulVec x - Bhat btil ι)) := by
    simp only [h1, h2, dotProduct, neg_mul, Finset.sum_neg_distrib]
  rw [hsum, ← Matrix.dotProduct_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hnonsing, Matrix.one_mulVec]
  simp only [Abar0Row, SurplusM, dotProduct_sub]
  ring

end RedCostPriv

theorem solution {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ)
    (M1 M2 : Finset (Fin n)) (ι : Fin n → M)
    (hbasic : (α, u, u0, v, v0, β) ∈ Set.extremePoints ℝ
      {w : (Fin n → ℝ) × (M → ℝ) × ℝ × (M → ℝ) × ℝ × ℝ |
        IsCGLPKFeasible Atil btil k w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2})
    (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ : M, u ρ ≠ 0 → ∃ j ∈ M1, ι j = ρ)
    (hv_supp : ∀ ρ : M, v ρ ≠ 0 → ∃ j ∈ M2, ι j = ρ)
    (hι_inj : Function.Injective ι) (hnonsing : IsUnit (Ahat Atil ι).det)
    (hM_disj : Disjoint M1 M2) (hM_cover : M1 ∪ M2 = Finset.univ)
    (i : M) (hi : ∀ j : Fin n, ι j ≠ i) (xbar : Fin n → ℝ) (ui vi : ℝ) :
    ObjExt Atil btil ι k M1 M2 i xbar ui vi =
      SigmaCoef Atil btil ι k M1 M2 xbar + ui * ReducedCostU Atil btil ι k M1 M2 xbar i +
        vi * ReducedCostV Atil btil ι k M1 M2 xbar i := by
  have hT := RedCostPriv.tableau_id Atil btil ι hnonsing i xbar
  rw [← hM_cover, Finset.sum_union hM_disj] at hT
  set D := 1 + ∑ j ∈ M1 ∪ M2, |Abar Atil ι k j| with hD
  have hDpos : 0 < D := by
    have : 0 ≤ ∑ j ∈ M1 ∪ M2, |Abar Atil ι k j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hD0 : D ≠ 0 := hDpos.ne'
  unfold ObjExt VExt V0Ext U0PlusV0Ext ReducedCostU ReducedCostV SigmaCoef
  rw [← hD]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  field_simp
  linear_combination (D * vi) * hT
