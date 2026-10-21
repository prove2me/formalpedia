-- Prove2me | solution 1 for BudgetedAffine.Budget.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:25:59.582085+00:00
-- url     : https://prove2.me/submissions/a2da969c-4dbe-4cc9-8de9-d87dd587aae5

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction

set_option autoImplicit false
open Matrix BudgetedAffine.Budget

theorem linMatrix_mulVec' {m n : ℕ} (I : Finset (Fin m)) (α : Fin m → ℝ) (v : Fin m → Fin n → ℝ)
    (h : Fin m → ℝ) : linMatrix I α v *ᵥ h = yLin I α v h := by
  funext j
  simp only [yLin, mulVec, dotProduct, linMatrix, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun i => i ∈ I) = I := by ext; simp
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem solution {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (w : Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ)
    (hopt : IsOptimalAR A B c d X (budgetSet w) xs ys)
    (OPT : ℝ) (hOPT : zAR A B c d X (budgetSet w) = (OPT : EReal))
    (v : Fin m → Fin n → ℝ)
    (hv : ∀ i ∈ Iset A B d w xs OPT, IsCoverOpt B d (Pi.single i 1) (v i))
    (xSta ySta : Fin n → ℝ)
    (hSta : IsStaticOpt A B c d X (staRhs (Iset A B d w xs OPT) (alpha A xs)) xSta ySta) :
    Feasible A B X (budgetSet w) xSta
      (fun h => linMatrix (Iset A B d w xs OPT) (alpha A xs) v *ᵥ h + ySta) := by
  obtain ⟨hxX, hy0, hrhs, -⟩ := hSta
  refine ⟨hxX, fun h hh => ?_⟩
  obtain ⟨hh01, -⟩ := hh
  set I := Iset A B d w xs OPT with hI
  have hα : ∀ i ∈ I, 0 < alpha A xs i := by
    intro i hi
    have := (Finset.mem_filter.1 hi).2.1
    exact this
  simp only [linMatrix_mulVec']
  have hvnn : ∀ i ∈ I, 0 ≤ v i := fun i hi => (hv i hi).1
  have hcov : ∀ i ∈ I, (Pi.single i (1:ℝ) : Fin m → ℝ) ≤ B *ᵥ v i := fun i hi => (hv i hi).2.1
  have hylin : 0 ≤ yLin I (alpha A xs) v h := by
    intro j
    simp only [yLin, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (mul_nonneg (hα i hi).le (hh01 i).1)
      (hvnn i hi j))
  refine ⟨fun j => add_nonneg (hylin j) (hy0 j), ?_⟩
  intro r
  have hBl : B *ᵥ yLin I (alpha A xs) v h = ∑ i ∈ I, ((alpha A xs i * h i) • (B *ᵥ v i)) := by
    simp only [yLin, Matrix.mulVec_sum, Matrix.mulVec_smul]
  rw [Matrix.mulVec_add, hBl]
  have hterm : ∀ i ∈ I, 0 ≤ (alpha A xs i * h i) * (B *ᵥ v i) r := by
    intro i hi
    refine mul_nonneg (mul_nonneg (hα i hi).le (hh01 i).1) ?_
    simp only [mulVec, dotProduct]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hB r j) (hvnn i hi j))
  have hsum : ∑ i ∈ I, (alpha A xs i * h i) * (B *ᵥ v i) r ≥ 0 := Finset.sum_nonneg hterm
  have hcomp : (A *ᵥ xSta + (∑ i ∈ I, ((alpha A xs i * h i) • (B *ᵥ v i)) + B *ᵥ ySta)) r =
      (A *ᵥ xSta + B *ᵥ ySta) r + ∑ i ∈ I, (alpha A xs i * h i) * (B *ᵥ v i) r := by
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcomp]
  have hr := hrhs r
  by_cases hrI : r ∈ I
  · have hst : staRhs I (alpha A xs) r = max (1 - alpha A xs r) 0 := by simp [staRhs, hrI]
    rw [hst] at hr
    have hsingle : (alpha A xs r * h r) * (B *ᵥ v r) r ≤
        ∑ i ∈ I, (alpha A xs i * h i) * (B *ᵥ v i) r :=
      Finset.single_le_sum (f := fun i => (alpha A xs i * h i) * (B *ᵥ v i) r) hterm hrI
    have hcv : (1:ℝ) ≤ (B *ᵥ v r) r := by
      have := hcov r hrI r
      simpa using this
    have hαr := hα r hrI
    have hh1 := hh01 r
    have hprod : alpha A xs r * h r ≤ (alpha A xs r * h r) * (B *ᵥ v r) r := by
      have : 0 ≤ alpha A xs r * h r := mul_nonneg hαr.le hh1.1
      nlinarith
    rcases le_total (alpha A xs r) 1 with hle | hle
    · have : 1 - alpha A xs r ≤ max (1 - alpha A xs r) 0 := le_max_left _ _
      nlinarith [mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 hh1.2)]
    · have : 0 ≤ max (1 - alpha A xs r) 0 := le_max_right _ _
      nlinarith [mul_nonneg (sub_nonneg.2 hle) hh1.1]
  · have hst : staRhs I (alpha A xs) r = 1 := by simp [staRhs, hrI]
    rw [hst] at hr
    linarith [(hh01 r).2]
