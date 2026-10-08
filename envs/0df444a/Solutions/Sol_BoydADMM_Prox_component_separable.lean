-- Prove2me | solution 1 for BoydADMM.Prox.component_separable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:25:09.922265+00:00
-- url     : https://prove2.me/submissions/0a662586-d362-42b1-94af-c543346a1d34

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix


namespace BoydADMM.Prox

theorem sep_identity {n p : ℕ} (A : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin n → ℝ) (hdiag : Aᵀ * A = Matrix.diagonal d)
    (v : EuclideanSpace ℝ (Fin p)) (y : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A y - v‖ ^ 2 =
      ∑ i, (d i * y i ^ 2 - 2 * (Matrix.toEuclideanLin Aᵀ v) i * y i) + ‖v‖ ^ 2 := by
  have nsq : ∀ {m : ℕ} (w : EuclideanSpace ℝ (Fin m)), ‖w‖ ^ 2 = ∑ i, (w i) ^ 2 := by
    intro m w; rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  rw [nsq, nsq]
  have hA : ∀ j, (Matrix.toEuclideanLin A y) j = (A *ᵥ y.ofLp) j := fun j => rfl
  have hAt : ∀ i, (Matrix.toEuclideanLin Aᵀ v) i = (Aᵀ *ᵥ v.ofLp) i := fun i => rfl
  simp only [PiLp.sub_apply, hA, hAt]
  set w := A *ᵥ y.ofLp
  have e1 : ∑ j, w j ^ 2 = ∑ i, d i * y i ^ 2 := by
    have : ∑ j, w j ^ 2 = w ⬝ᵥ w := by simp [dotProduct, sq]
    rw [this]
    have h2 : w ⬝ᵥ w = (Aᵀ *ᵥ w) ⬝ᵥ y.ofLp := by
      rw [show w ⬝ᵥ w = w ⬝ᵥ A *ᵥ y.ofLp from rfl, dotProduct_mulVec, mulVec_transpose]
    rw [h2, show w = A *ᵥ y.ofLp from rfl, mulVec_mulVec, hdiag]
    simp [dotProduct, mulVec_diagonal, sq]
    apply Finset.sum_congr rfl; intro i _; ring
  have e2 : ∑ j, w j * v j = ∑ i, (Aᵀ *ᵥ v.ofLp) i * y i := by
    have : ∑ j, w j * v j = v.ofLp ⬝ᵥ (A *ᵥ y.ofLp) := by
      simp [dotProduct, w, mul_comm]
    rw [this, dotProduct_mulVec, ← mulVec_transpose]
    simp [dotProduct]
  have : ∑ j, (w j - v j) ^ 2 = ∑ j, w j ^ 2 - 2 * ∑ j, w j * v j + ∑ j, v j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [this, e1, e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro i _; ring

theorem sep_core {n p : ℕ} (f : Fin n → ℝ → ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin n → ℝ) (hdiag : Aᵀ * A = Matrix.diagonal d) (ρ : ℝ) (hρ : 0 < ρ)
    (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)) :
    IsXUpdate Set.univ (fun y => ∑ i, f i (y i)) ρ A v x ↔
      ∀ i, ∀ t : ℝ,
        f i (x i) + (ρ / 2) * (d i * x i ^ 2 - 2 * (Matrix.toEuclideanLin Aᵀ v) i * x i) ≤
          f i t + (ρ / 2) * (d i * t ^ 2 - 2 * (Matrix.toEuclideanLin Aᵀ v) i * t) := by
  set b := Matrix.toEuclideanLin Aᵀ v
  set g : Fin n → ℝ → ℝ := fun i t => f i t + (ρ / 2) * (d i * t ^ 2 - 2 * b i * t) with hg
  have key : ∀ y : EuclideanSpace ℝ (Fin n),
      (∑ i, f i (y i)) + (ρ / 2) * ‖Matrix.toEuclideanLin A y - v‖ ^ 2 =
        ∑ i, g i (y i) + (ρ / 2) * ‖v‖ ^ 2 := by
    intro y
    rw [sep_identity A d hdiag v y, mul_add, Finset.mul_sum, hg]
    simp only [Finset.sum_add_distrib]
    ring
  unfold IsXUpdate
  simp only [Set.mem_univ, true_and, forall_const, key]
  constructor
  · intro h i t
    have := h (WithLp.toLp 2 (Function.update x.ofLp i t))
    have hsplit : ∀ z : EuclideanSpace ℝ (Fin n),
        ∑ j, g j (z j) = g i (z i) + ∑ j ∈ Finset.univ.erase i, g j (z j) := fun z =>
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    rw [hsplit x, hsplit (WithLp.toLp 2 (Function.update x.ofLp i t))] at this
    have hrest : ∑ j ∈ Finset.univ.erase i, g j ((WithLp.toLp 2 (Function.update x.ofLp i t) :
        EuclideanSpace ℝ (Fin n)) j) = ∑ j ∈ Finset.univ.erase i, g j (x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have : j ≠ i := Finset.ne_of_mem_erase hj
      simp [Function.update_of_ne this]
    rw [hrest] at this
    have hi : (WithLp.toLp 2 (Function.update x.ofLp i t) : EuclideanSpace ℝ (Fin n)) i = t := by
      simp
    rw [hi] at this
    show g i (x i) ≤ g i t
    linarith
  · intro h y
    have : ∑ i, g i (x i) ≤ ∑ i, g i (y i) := Finset.sum_le_sum fun i _ => h i (y i)
    linarith

end BoydADMM.Prox

open BoydADMM.Prox


theorem solution {n p : ℕ} (f : Fin n → ℝ → ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin n → ℝ) (hdiag : Aᵀ * A = Matrix.diagonal d) (ρ : ℝ) (hρ : 0 < ρ)
    (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)) :
    IsXUpdate Set.univ (fun y => ∑ i, f i (y i)) ρ A v x ↔
      ∀ i, ∀ t : ℝ,
        f i (x i) + (ρ / 2) * (d i * x i ^ 2 - 2 * (Matrix.toEuclideanLin Aᵀ v) i * x i) ≤
          f i t + (ρ / 2) * (d i * t ^ 2 - 2 * (Matrix.toEuclideanLin Aᵀ v) i * t) := by
  exact sep_core f A d hdiag ρ hρ v x
