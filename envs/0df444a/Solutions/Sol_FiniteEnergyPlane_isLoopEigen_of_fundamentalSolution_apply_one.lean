-- Prove2me | solution 1 for FiniteEnergyPlane.isLoopEigen_of_fundamentalSolution_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T22:43:27.146217+00:00
-- url     : https://prove2.me/submissions/594f81ca-b702-44be-a3fd-878062110308

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_FiniteEnergyPlane_contDiff_of_hasDerivAt_clm_apply
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Matrix.Normed



namespace FiniteEnergyPlane

open Matrix
open scoped ContDiff

theorem isLoopEigen_of_fundamentalSolution_apply_one_aux {n : ℕ}
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (μ : ℝ)
    (Ψ : ℝ → CauchyRiemannIndex.Mat n)
    (hΨ : CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat n)) Ψ)
    (v : CauchyRiemannIndex.Vec n) (hv : v ≠ 0) (h1 : Matrix.toEuclideanLin (Ψ 1) v = v) :
    IsLoopEigen Sinf μ (fun t => Matrix.toEuclideanLin (Ψ t) v) := by
  let _ : NormedAddCommGroup (CauchyRiemannIndex.Mat n) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (CauchyRiemannIndex.Mat n) := Matrix.normedSpace
  obtain ⟨hΨ0, hΨd⟩ := hΨ
  set M : ℝ → CauchyRiemannIndex.Mat n := fun t =>
    CauchyRiemannIndex.J₀ n * (Sinf t + μ • (1 : CauchyRiemannIndex.Mat n)) with hM
  let Lv : CauchyRiemannIndex.Mat n →ₗ[ℝ] CauchyRiemannIndex.Vec n :=
    { toFun := fun N => Matrix.toEuclideanLin N v
      map_add' := fun N N' => by simp
      map_smul' := fun c N => by simp }
  have hx : ∀ t, HasDerivAt (fun t => Matrix.toEuclideanLin (Ψ t) v)
      (Matrix.toEuclideanLin (M t * Ψ t) v) t := fun t =>
    (LinearMap.toContinuousLinearMap Lv).hasFDerivAt.comp_hasDerivAt t (hΨd t)
  -- the eigenvalue equation
  have heq : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n)
      (deriv (fun t => Matrix.toEuclideanLin (Ψ t) v) t)) -
        Matrix.toEuclideanLin (Sinf t) (Matrix.toEuclideanLin (Ψ t) v) =
      μ • Matrix.toEuclideanLin (Ψ t) v := by
    intro t
    rw [(hx t).deriv]
    have hJ : CauchyRiemannIndex.J₀ n * CauchyRiemannIndex.J₀ n = -1 := Matrix.J_squared _ _
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, hM]
    have hm : (CauchyRiemannIndex.J₀ n * (Sinf t + μ • 1) * Ψ t) *ᵥ WithLp.ofLp v =
        CauchyRiemannIndex.J₀ n *ᵥ (Sinf t *ᵥ (Ψ t *ᵥ WithLp.ofLp v) +
          μ • (Ψ t *ᵥ WithLp.ofLp v)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hm, Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]
    ext i
    simp
  -- Floquet: `Ψ (t + 1) = Ψ t * Ψ 1`
  have hcont : Continuous fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat n) :=
    hSinf.1.add continuous_const
  obtain ⟨Ψ₀, -, huniq⟩ := CauchyRiemannIndex.fundamentalSolution_existsUnique n _ hcont
  have hsymm : ∀ t, (Sinf t + μ • (1 : CauchyRiemannIndex.Mat n)).IsSymm := by
    intro t
    exact (hSinf.2.2 t).add (Matrix.isSymm_one.smul μ)
  have hdet : IsUnit (Ψ 1).det :=
    SymplecticGroup.symplectic_det (CauchyRiemannIndex.fundamentalSolution_symplectic n _ hsymm
      Ψ ⟨hΨ0, hΨd⟩ 1)
  have hfl : ∀ t, Ψ (t + 1) = Ψ t * Ψ 1 := by
    set Φ : ℝ → CauchyRiemannIndex.Mat n := fun t => Ψ (t + 1) * (Ψ 1)⁻¹ with hΦ
    have hΦfs : CauchyRiemannIndex.IsFundamentalSolution
        (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat n)) Φ := by
      refine ⟨by simp [hΦ, Matrix.mul_nonsing_inv _ hdet], fun t => ?_⟩
      have h := (hΨd (t + 1)).comp_add_const t 1
      have hR := (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ
        (Ψ 1)⁻¹)).hasFDerivAt.comp_hasDerivAt t h
      simp only [Function.comp_def, LinearMap.coe_toContinuousLinearMap',
        LinearMap.mulRight_apply] at hR
      refine hR.congr_deriv ?_
      have hS1 : Sinf (t + 1) = Sinf t := hSinf.2.1 t
      simp only [hΦ, hS1, Matrix.mul_assoc]
      show (CauchyRiemannIndex.J₀ n * ((Sinf t + μ • 1) * Ψ (t + 1))) * (Ψ 1)⁻¹ = _
      simp only [Matrix.mul_assoc]
    have e1 := huniq Φ hΦfs
    have e2 := huniq Ψ ⟨hΨ0, hΨd⟩
    intro t
    have : Φ t = Ψ t := by rw [e1, e2]
    calc Ψ (t + 1) = Φ t * Ψ 1 := by
          simp only [hΦ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
      _ = Ψ t * Ψ 1 := by rw [this]
  -- smoothness
  have hsmooth : ContDiff ℝ ∞ (fun t => Matrix.toEuclideanLin (Ψ t) v) := by
    let Φl : CauchyRiemannIndex.Mat n →ₗ[ℝ]
        (CauchyRiemannIndex.Vec n →L[ℝ] CauchyRiemannIndex.Vec n) :=
      { toFun := fun N => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)
        map_add' := fun N N' => by ext x : 1; simp
        map_smul' := fun c N => by ext x : 1; simp }
    have hMs : ContDiff ℝ ∞ M := by
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
      simp only [hM, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact ContDiff.sum fun k _ => contDiff_const.mul ((hSinf' k j).add contDiff_const)
    refine contDiff_of_hasDerivAt_clm_apply (fun t => Φl (M t))
      ((LinearMap.toContinuousLinearMap Φl).contDiff.comp hMs) _ fun t => (hx t).congr_deriv ?_
    simp [Φl, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  refine ⟨hsmooth, fun t => ?_, ⟨0, by simpa [hΨ0] using hv⟩, heq⟩
  show Matrix.toEuclideanLin (Ψ (t + 1)) v = Matrix.toEuclideanLin (Ψ t) v
  rw [hfl t, Matrix.toLpLin_mul]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [h1]

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution {n : ℕ}
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (μ : ℝ)
    (Ψ : ℝ → CauchyRiemannIndex.Mat n)
    (hΨ : CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat n)) Ψ)
    (v : CauchyRiemannIndex.Vec n) (hv : v ≠ 0) (h1 : Matrix.toEuclideanLin (Ψ 1) v = v) :
    IsLoopEigen Sinf μ (fun t => Matrix.toEuclideanLin (Ψ t) v) :=
  isLoopEigen_of_fundamentalSolution_apply_one_aux Sinf hSinf hSinf' μ Ψ hΨ v hv h1
