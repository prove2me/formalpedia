-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadOpMat_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T05:49:16.316373+00:00
-- url     : https://prove2.me/submissions/a49d0ec5-e618-41c6-a096-6aabe2236113

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Theorems.Thm_BookProof_QuadraticRotation_exists_rotConj_eigenvalues
import Theorems.Thm_BookProof_QuadraticRotation_quadPolyMat_rotPoly
import Theorems.Thm_BookProof_QuadraticRotation_orthonormal_rotHermiteLp
import Theorems.Thm_BookProof_QuadraticRotation_span_rotHermiteLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_deficiencyTrivialAt_of_diagonal
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadPoly_hermiteMv
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreOp_coe
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreEquiv_coe
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_pgLp_smul
import Theorems.Thm_BookProof_HyperbolicQuadratic_polyGaussCore_dense_L2

import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem qrot_eig {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ)
    (a : Fin d →₀ ℕ) (h : rotHermiteLp O a ∈ polyGaussCore (d := d)) :
    quadOpMat (rotConj O c) ⟨rotHermiteLp O a, h⟩
      = ((BookProof.HyperbolicQuadratic.quadSymbol c a : ℝ) : ℂ) • rotHermiteLp O a := by
  set p : MvPolynomial (Fin d) ℂ := ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • rotPoly O (hermiteMv a) with hp
  have hv : rotHermiteLp O a = pgLp p := by
    rw [hp, BookProof.NavierStokesFlow.DifferentialL2.pgLp_smul]; rfl
  have he : (⟨rotHermiteLp O a, h⟩ : polyGaussCore (d := d)) = coreEquiv p := by
    apply Subtype.ext
    rw [BookProof.NavierStokesFlow.DifferentialL2.coreEquiv_coe]; exact hv
  rw [he]
  change ((coreOp (quadPolyMat (rotConj O c)) (coreEquiv p) : polyGaussCore (d := d)) : L2d d) = _
  rw [BookProof.NavierStokesFlow.DifferentialL2.coreOp_coe, hv, hp, map_smul,
    BookProof.QuadraticRotation.quadPolyMat_rotPoly hO,
    BookProof.HyperbolicQuadratic.quadPoly_hermiteMv, map_smul, smul_comm,
    BookProof.NavierStokesFlow.DifferentialL2.pgLp_smul]

theorem solution {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOpMat A) := by
  obtain ⟨O, hO, hAO⟩ := BookProof.QuadraticRotation.exists_rotConj_eigenvalues hA
  rw [hAO]
  have hspan := BookProof.QuadraticRotation.span_rotHermiteLp (d := d) hO
  have hmem : ∀ a, rotHermiteLp O a ∈ polyGaussCore (d := d) := by
    intro a; rw [← hspan]; exact Submodule.subset_span ⟨a, rfl⟩
  have htot : ∀ w : L2d d, (∀ a, (inner ℂ (rotHermiteLp O a) w : ℂ) = 0) → w = 0 := by
    intro w hw
    have hcore : ∀ u ∈ polyGaussCore (d := d), (inner ℂ u w : ℂ) = 0 := by
      intro u hu
      rw [← hspan] at hu
      induction hu using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hw a
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]
    have hext : (fun u : L2d d => (inner ℂ u w : ℂ)) = fun _ => 0 :=
      Continuous.ext_on BookProof.HyperbolicQuadratic.polyGaussCore_dense_L2
        (continuous_id.inner continuous_const) continuous_const (fun u hu => hcore u hu)
    have := congrFun hext w
    exact inner_self_eq_zero.mp this
  exact ⟨BookProof.HyperbolicQuadratic.deficiencyTrivialAt_of_diagonal (rotHermiteLp O)
      (BookProof.HyperbolicQuadratic.quadSymbol hA.eigenvalues) htot _ hmem
      (qrot_eig hO hA.eigenvalues) (by simp),
    BookProof.HyperbolicQuadratic.deficiencyTrivialAt_of_diagonal (rotHermiteLp O)
      (BookProof.HyperbolicQuadratic.quadSymbol hA.eigenvalues) htot _ hmem
      (qrot_eig hO hA.eigenvalues) (by simp)⟩
