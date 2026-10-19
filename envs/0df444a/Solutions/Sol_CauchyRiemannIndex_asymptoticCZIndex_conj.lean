-- Prove2me | solution 1 for CauchyRiemannIndex.asymptoticCZIndex_conj
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T10:50:22.856997+00:00
-- url     : https://prove2.me/submissions/8ea916a6-55d0-45d0-82b2-12b5233d061f

import Theorems.Thm_CauchyRiemannIndex_czIndex_conj_path
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_czIndex
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Instances.Matrix

namespace CauchyRiemannIndex

open Matrix

lemma crm_CC (n : ℕ) : conjMat n * conjMat n = 1 := by
  simp [conjMat, fromBlocks_multiply, ← fromBlocks_one]

lemma crm_CJ (n : ℕ) : conjMat n * J₀ n = -(J₀ n * conjMat n) := by
  simp [conjMat, J₀, Matrix.J, fromBlocks_multiply, fromBlocks_neg]

lemma crm_CT (n : ℕ) : (conjMat n)ᵀ = conjMat n := by
  simp [conjMat, fromBlocks_transpose]

/-- `t ↦ C Ψ(t) C` is the fundamental solution of `t ↦ -(C S(t) C)`. -/
lemma crm_fund (n : ℕ) (S Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ) :
    IsFundamentalSolution (fun t => -(conjMat n * S t * conjMat n))
      (fun t => conjMat n * Ψ t * conjMat n) := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  set C := conjMat n
  have hCC : C * C = 1 := crm_CC n
  refine ⟨by simp [hΨ.1, hCC], fun t => ?_⟩
  have hCJ : C * J₀ n = -(J₀ n * C) := crm_CJ n
  have hd := ((hΨ.2 t).const_mul C).mul_const C
  refine hd.congr_deriv ?_
  calc C * (J₀ n * S t * Ψ t) * C = C * J₀ n * S t * Ψ t * C := by noncomm_ring
    _ = -(J₀ n * (C * S t * C) * (C * Ψ t * C)) := by
        rw [hCJ]
        calc -(J₀ n * C) * S t * Ψ t * C = -(J₀ n * C * S t * (1 : Mat n) * Ψ t * C) := by
              noncomm_ring
          _ = -(J₀ n * (C * S t * C) * (C * Ψ t * C)) := by rw [← hCC]; noncomm_ring
    _ = J₀ n * -(C * S t * C) * (C * Ψ t * C) := by noncomm_ring

lemma crm_symLoop (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S) :
    IsSymLoop (fun t => -(conjMat n * S t * conjMat n)) := by
  refine ⟨((continuous_const.matrix_mul hS.1).matrix_mul continuous_const).neg,
    fun t => by simp only [hS.2.1 t], fun t => ?_⟩
  show (-(conjMat n * S t * conjMat n))ᵀ = -(conjMat n * S t * conjMat n)
  rw [transpose_neg, transpose_mul, transpose_mul, crm_CT, (hS.2.2 t).eq, Matrix.mul_assoc]

end CauchyRiemannIndex

open CauchyRiemannIndex Matrix in
theorem solution (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hn : IsNondegenerate S) :
    IsNondegenerate (fun t => -(conjMat n * S t * conjMat n)) ∧
      asymptoticCZIndex (fun t => -(conjMat n * S t * conjMat n)) = -asymptoticCZIndex S := by
  obtain ⟨Ψ, hΨ, -⟩ := fundamentalSolution_existsUnique n S hS.1
  have hSb := crm_symLoop n S hS
  have hΦ := crm_fund n S Ψ hΨ
  have hnb : IsNondegenerate (fun t => -(conjMat n * S t * conjMat n)) := by
    intro Ψ' hΨ'
    have he := (fundamentalSolution_existsUnique n _ hSb.1).unique hΨ' hΦ
    subst he
    have : (1 : Mat n) - conjMat n * Ψ 1 * conjMat n = conjMat n * (1 - Ψ 1) * conjMat n := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, crm_CC]
    show (1 - conjMat n * Ψ 1 * conjMat n).det ≠ 0
    rw [this, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, crm_CC, det_one, one_mul]
    exact hn Ψ hΨ
  refine ⟨hnb, ?_⟩
  have hcΨ : Continuous Ψ := by
    letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
    exact continuous_iff_continuousAt.2 fun t => (hΨ.2 t).continuousAt
  let ψ : C(unitInterval, Mat n) := ⟨fun t => Ψ t, hcΨ.comp continuous_subtype_val⟩
  let φ : C(unitInterval, Mat n) :=
    ⟨fun t => conjMat n * Ψ t * conjMat n,
      ((continuous_const.matrix_mul hcΨ).matrix_mul continuous_const).comp continuous_subtype_val⟩
  rw [asymptoticCZIndex_eq_czIndex n S hS hn Ψ hΨ ψ (fun _ => rfl),
    asymptoticCZIndex_eq_czIndex n _ hSb hnb _ hΦ φ (fun _ => rfl)]
  exact czIndex_conj_path n ψ φ (fun t => fundamentalSolution_symplectic n S hS.2.2 Ψ hΨ t)
    (by simpa [ψ] using hΨ.1) (by simpa [ψ] using hn Ψ hΨ) (fun _ => rfl)
