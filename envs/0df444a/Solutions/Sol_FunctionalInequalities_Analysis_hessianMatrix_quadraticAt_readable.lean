-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hessianMatrix_quadraticAt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:20.313371+00:00
-- url     : https://prove2.me/submissions/f61c0a03-f42c-4e00-a85a-2ce29441da66

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12E1AlexandrovPointEquation
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
/-- `quadraticAt A x₀ b c` is smooth (weak Letwin route). -/
theorem FunctionalInequalities.Analysis.contDiff_quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) : ContDiff ℝ 2 (quadraticAt A x₀ b c) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  change ContDiff ℝ 2
    (fun x => c + ⟪b, x - x₀⟫ + (1 / 2 : ℝ) * ⟪x - x₀, T (x - x₀)⟫)
  exact (contDiff_const.add
    (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))).add
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).inner ℝ
      (T.contDiff.comp (contDiff_id.sub contDiff_const))))
private lemma FunctionalInequalities.Analysis.quadraticAt_fderiv_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (y w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (quadraticAt A x₀ b c) y w =
      ⟪b, w⟫ + (1 / 2 : ℝ) *
        (⟪y - x₀, Matrix.toEuclideanLin A w⟫ +
          ⟪w, Matrix.toEuclideanLin A (y - x₀)⟫) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hd := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x₀
  have ht := T.hasFDerivAt.comp y hd
  have hb := (hasFDerivAt_const (𝕜 := ℝ) b y).inner ℝ hd
  have hq := hd.inner ℝ ht
  have hh := (hb.const_add c).add (hq.const_mul (1 / 2 : ℝ))
  change HasFDerivAt (quadraticAt A x₀ b c) _ y at hh
  rw [hh.fderiv]
  simp [fderivInnerCLM_apply, T]
private lemma FunctionalInequalities.Analysis.quadraticAt_second_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ w x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ
      (fun y => (1 / 2 : ℝ) *
        (⟪y - x₀, Matrix.toEuclideanLin A w⟫ +
          ⟪w, Matrix.toEuclideanLin A (y - x₀)⟫)) x v =
      (1 / 2 : ℝ) *
        (⟪v, Matrix.toEuclideanLin A w⟫ + ⟪w, Matrix.toEuclideanLin A v⟫) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hd := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀
  have ht := T.hasFDerivAt.comp x hd
  have h₁ := hd.inner ℝ (hasFDerivAt_const (𝕜 := ℝ) (T w) x)
  have h₂ := (hasFDerivAt_const (𝕜 := ℝ) w x).inner ℝ ht
  have hh := (h₁.add h₂).const_mul (1 / 2 : ℝ)
  simpa [fderivInnerCLM_apply, T, mul_add] using
    congrArg (fun L => L v) hh.fderiv
private lemma FunctionalInequalities.Analysis.quadraticAt_basis_entry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Matrix.toEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = A i j := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, Matrix.toLpLin_apply 2 2]
  simp [Matrix.mulVec, dotProduct]
/-- The coordinate Hessian of `quadraticAt A x₀ b c` is `A` at every point when `A` is symmetric
(weak Letwin route). -/
theorem solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    FunctionalInequalities.Probability.Stein.hessianMatrix (FunctionalInequalities.Analysis.quadraticAt A x₀ b c) x = A := by
  ext i j
  change bilinearIteratedFDerivTwo ℝ (FunctionalInequalities.Analysis.quadraticAt A x₀ b c) x
    (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j) = A i j
  rw [FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
    (FunctionalInequalities.Analysis.contDiff_quadraticAt A x₀ b c)]
  simp_rw [FunctionalInequalities.Analysis.quadraticAt_fderiv_apply]
  rw [fderiv_const_add, FunctionalInequalities.Analysis.quadraticAt_second_apply,
    FunctionalInequalities.Analysis.quadraticAt_basis_entry, FunctionalInequalities.Analysis.quadraticAt_basis_entry]
  have hs : A j i = A i j := by simpa using hA.apply i j
  rw [hs]
  ring
