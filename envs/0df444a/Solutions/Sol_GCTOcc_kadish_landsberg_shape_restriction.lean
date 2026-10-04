-- Prove2me | solution 1 for GCTOcc.kadish_landsberg_shape_restriction
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:39:54.091686+00:00
-- url     : https://prove2.me/submissions/5f7c1d1b-fe53-4d99-b6dc-8a01e479a1f7

import Mathlib
import Definitions.Def_GCTOcc_occurrence

set_option autoImplicit false

namespace KLCex27

open GCTOcc MvPolynomial

/-- The witness weight `(1, 0, 0, …)`. -/
def lam0 : ℕ → ℕ := fun i => if i = 0 then 1 else 0

/-- The monomial `X (0,0)`. -/
noncomputable def s0 : (ℕ × ℕ) →₀ ℕ := Finsupp.single (0, 0) 1

/-- The highest weight vector: the coordinate function reading off the coefficient of `X (0,0)`. -/
noncomputable def F0 : CoordRing := X s0

theorem permPoly_zero : permPoly 0 = 1 := by
  simp [permPoly]

theorem paddedPerm_zero_one : paddedPerm 0 1 = X (0, 0) := by
  simp [paddedPerm, permPoly_zero]

theorem form_one_eq (p : PolyR) (hp : IsForm 1 p) : p = C (coeff s0 p) * X (0, 0) := by
  ext m
  rw [coeff_C_mul, coeff_X']
  change coeff m p = coeff s0 p * if s0 = m then 1 else 0
  split_ifs with hm
  · subst hm; simp
  · rw [mul_zero]
    by_contra h
    have hmem : m ∈ p.support := mem_support_iff.mpr h
    have hsupp := hp.2 m hmem
    have hm' : m = Finsupp.single (0, 0) (m (0, 0)) := by
      ext v
      by_cases hv : v = (0, 0)
      · subst hv; simp
      · rw [Finsupp.single_apply, if_neg (fun h => hv h.symm)]
        by_contra hv0
        have := hsupp v (Finsupp.mem_support_iff.mpr hv0)
        exact hv (Prod.ext (Nat.lt_one_iff.mp this.1) (Nat.lt_one_iff.mp this.2))
    have hdeg := hp.1 h
    rw [hm'] at hdeg
    have h1 : m (0, 0) = 1 := by simpa [Finsupp.weight_apply] using hdeg
    apply hm
    rw [hm', h1]
    rfl

theorem substLin_X00 (g : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) :
    substLin 1 g (X (0, 0)) = C (g (0, 0) (0, 0)) * X (0, 0) := by
  simp [substLin]
  rw [Fintype.sum_eq_single ((0 : Fin 1), (0 : Fin 1))]
  intro x hx
  exact absurd (Prod.ext (Fin.fin_one_eq_zero _) (Fin.fin_one_eq_zero _)) hx

theorem substLin_CX (g : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) (c : ℂ) :
    substLin 1 g (C c * X (0, 0)) = C (c * g (0, 0) (0, 0)) * X (0, 0) := by
  have h := substLin_X00 g
  unfold substLin at h ⊢
  rw [map_mul, aeval_C, h, algebraMap_eq, C_mul, mul_assoc]

theorem eval_CX (a : ℂ) : evalCoeff (C a * X (0, 0)) F0 = a := by
  simp [evalCoeff, F0, s0, coeff_C_mul, coeff_X]

theorem prod_eq (g : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) :
    (∏ v : Fin 1 × Fin 1, g v v ^ lam0 (idx 1 v)) = g (0, 0) (0, 0) := by
  rw [Fintype.prod_eq_single ((0 : Fin 1), (0 : Fin 1))]
  · simp [lam0, idx]
  · intro x hx
    exact absurd (Prod.ext (Fin.fin_one_eq_zero _) (Fin.fin_one_eq_zero _)) hx

theorem hwv : IsHWV 1 1 lam0 F0 := by
  refine ⟨isHomogeneous_X _ _, ?_⟩
  intro g _ _ p hp
  rw [form_one_eq p hp, substLin_CX, eval_CX, eval_CX, prod_eq, mul_comm]

theorem part : IsPartitionOf lam0 (1 * 1) (1 * 1) := by
  refine ⟨fun i => ?_, fun i hi => ?_, ?_⟩
  · show (if i + 1 = 0 then 1 else 0) ≤ (if i = 0 then 1 else 0)
    rw [if_neg (by omega)]
    exact Nat.zero_le _
  · show (if i = 0 then 1 else 0) = 0
    rw [if_neg (by omega)]
  · simp [lam0]

theorem mem : (X (0, 0) : PolyR) ∈ orbitClosure 1 (paddedPerm 0 1) := by
  refine ⟨fun _ => 1, fun _ => by simp, fun m => ?_⟩
  simp only [paddedPerm_zero_one, substLin_X00, Matrix.one_apply_eq, map_one, one_mul]
  exact tendsto_const_nhds

theorem occ : Occurs 1 1 lam0 (orbitClosure 1 (paddedPerm 0 1)) := by
  refine ⟨F0, hwv, X (0, 0), mem, ?_⟩
  rw [show (X (0, 0) : PolyR) = C 1 * X (0, 0) by simp, eval_CX]
  exact one_ne_zero

end KLCex27

open GCTOcc MvPolynomial in
theorem solution : ¬ (∀ (n d m : ℕ) (lam : ℕ → ℕ), IsPartitionOf lam (n * n) (n * d) →
    Occurs n d lam (orbitClosure n (paddedPerm m n)) →
    (∀ i, m * m ≤ i → lam i = 0) ∧ (∑ i ∈ Finset.range (n * n), lam (i + 1)) ≤ m * d) := by
  intro H
  have h := (H 1 1 0 KLCex27.lam0 KLCex27.part KLCex27.occ).1 0 (le_refl _)
  simp [KLCex27.lam0] at h
