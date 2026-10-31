-- Prove2me | solution 1 for CauchyRiemannIndex.isNondegenerate_smul_comp_affine
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T09:29:10.9537+00:00
-- url     : https://prove2.me/submissions/c53f9dc5-9888-4473-b319-b6bebbb3834a

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse



namespace CauchyRiemannIndex

open Matrix

lemma kn3_isUnit {n : ℕ} {A : Mat n} (hA : IsSymplectic A) : IsUnit A.det := by
  have h : IsUnit (⟨A, hA⟩ : Matrix.symplecticGroup (Fin n) ℝ) := Group.isUnit _
  exact (Matrix.isUnit_iff_isUnit_det A).1 (h.map (Matrix.symplecticGroup (Fin n) ℝ).subtype)

/-- Reparametrized and renormalized fundamental solutions. -/
lemma kn3_fund_affine {n : ℕ} (S : ℝ → Mat n) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ)
    (ε c : ℝ) (hc : IsUnit (Ψ c).det) :
    IsFundamentalSolution (fun t => ε • S (ε * t + c)) (fun t => Ψ (ε * t + c) * (Ψ c)⁻¹) := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  refine ⟨?_, fun t => ?_⟩
  · show Ψ (ε * 0 + c) * (Ψ c)⁻¹ = 1
    rw [mul_zero, zero_add]
    exact Matrix.mul_nonsing_inv _ hc
  have hb : HasDerivAt (fun t : ℝ => ε * t + c) ε t := by
    have := ((hasDerivAt_id t).const_mul ε).add_const c
    rwa [mul_one] at this
  have h := ((hΨ.2 (ε * t + c)).scomp t hb).mul_const (Ψ c)⁻¹
  have e : (ε • (J₀ n * S (ε * t + c) * Ψ (ε * t + c))) * (Ψ c)⁻¹ =
      J₀ n * (ε • S (ε * t + c)) * (Ψ (ε * t + c) * (Ψ c)⁻¹) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, mul_assoc]
  rw [e] at h
  exact h

lemma kn3_period {n : ℕ} (S : ℝ → Mat n) (hS : IsSymLoop S) (Ψ : ℝ → Mat n)
    (hΨ : IsFundamentalSolution S Ψ) (t : ℝ) : Ψ (t + 1) = Ψ t * Ψ 1 := by
  have hu : ∀ t, IsUnit (Ψ t).det := fun t =>
    kn3_isUnit (fundamentalSolution_symplectic n S hS.2.2 Ψ hΨ t)
  have h1 := kn3_fund_affine S Ψ hΨ 1 1 (hu 1)
  have hS1 : (fun t => (1 : ℝ) • S (1 * t + 1)) = S := by
    funext t; rw [one_smul, one_mul]; exact hS.2.1 t
  rw [hS1] at h1
  have hEq := (fundamentalSolution_existsUnique n S hS.1).unique h1 hΨ
  have ht := congrFun hEq t
  simp only [one_mul] at ht
  rw [← ht, Matrix.nonsing_inv_mul_cancel_right _ _ (hu 1)]

theorem isNondegenerate_smul_comp_affine_aux (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) (ε c : ℝ) (hε : ε = 1 ∨ ε = -1) :
    IsSymLoop (fun t => ε • Sinf (ε * t + c)) ∧ IsNondegenerate (fun t => ε • Sinf (ε * t + c)) := by
  have hper1 : ∀ x, Sinf (x + ε) = Sinf x := by
    intro x
    rcases hε with rfl | rfl
    · exact hS.2.1 x
    · rw [← sub_eq_add_neg]; exact hS.2.1.sub_eq x
  have hcont : Continuous (fun t => ε • Sinf (ε * t + c)) :=
    (hS.1.comp ((continuous_const.mul continuous_id).add continuous_const)).const_smul ε
  refine ⟨⟨hcont, fun t => ?_, fun t => (hS.2.2 _).smul ε⟩, ?_⟩
  · show ε • Sinf (ε * (t + 1) + c) = ε • Sinf (ε * t + c)
    rw [show ε * (t + 1) + c = (ε * t + c) + ε by ring, hper1]
  intro Φ hΦ
  obtain ⟨Ψ, hΨ, -⟩ := fundamentalSolution_existsUnique n Sinf hS.1
  have hu : ∀ t, IsUnit (Ψ t).det := fun t =>
    kn3_isUnit (fundamentalSolution_symplectic n Sinf hS.2.2 Ψ hΨ t)
  have h0 := kn3_fund_affine Sinf Ψ hΨ ε c (hu c)
  rw [(fundamentalSolution_existsUnique n _ hcont).unique hΦ h0]
  show (1 - Ψ (ε * 1 + c) * (Ψ c)⁻¹).det ≠ 0
  have hP := kn3_period Sinf hS Ψ hΨ
  have hcu : IsUnit (Ψ c) := (Matrix.isUnit_iff_isUnit_det _).2 (hu c)
  have conj : ∀ M : Mat n, 1 - Ψ c * M * (Ψ c)⁻¹ = Ψ c * (1 - M) * (Ψ c)⁻¹ := by
    intro M
    rw [mul_sub, sub_mul, mul_one, Matrix.mul_nonsing_inv _ (hu c)]
  rcases hε with rfl | rfl
  · rw [one_mul, add_comm, hP c, conj, Matrix.det_conj hcu]
    exact hnd Ψ hΨ
  · have h1 : Ψ (-1 * 1 + c) = Ψ c * (Ψ 1)⁻¹ := by
      have := hP (c - 1)
      rw [sub_add_cancel] at this
      rw [this, show -1 * 1 + c = c - 1 by ring, Matrix.mul_nonsing_inv_cancel_right _ _ (hu 1)]
    rw [h1, conj, Matrix.det_conj hcu]
    have e : 1 - (Ψ 1)⁻¹ = -(1 - Ψ 1) * (Ψ 1)⁻¹ := by
      rw [neg_sub, sub_mul, one_mul, Matrix.mul_nonsing_inv _ (hu 1)]
    rw [e, Matrix.det_mul, Matrix.det_neg]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hnd Ψ hΨ))
      (Matrix.isUnit_nonsing_inv_det _ (hu 1)).ne_zero

end CauchyRiemannIndex

open CauchyRiemannIndex

open Matrix

theorem solution (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) (ε c : ℝ) (hε : ε = 1 ∨ ε = -1) :
    IsSymLoop (fun t => ε • Sinf (ε * t + c)) ∧ IsNondegenerate (fun t => ε • Sinf (ε * t + c)) :=
  isNondegenerate_smul_comp_affine_aux n Sinf hS hnd ε c hε
