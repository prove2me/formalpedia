-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_hasZeroDeficiencyOn_of_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:30:30.771596+00:00
-- url     : https://prove2.me/submissions/4f6c46bb-564a-4db2-b1d7-21276b1c9e44

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_hasZeroDeficiencyOn_of_eigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)
set_option autoImplicit false

theorem solution {I : Type*} (e : I → c.D) (lam : I → ℝ)
    (heig : ∀ i, c.comparison (e i) = ((lam i : ℂ)) • e i)
    (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : c.D) : F) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn c.D c.comparison := by
  have hscalar (a : ℝ) (z : ℂ) (h : (a : ℂ) * z = Complex.I * z ∨ (a : ℂ) * z = -(Complex.I * z)) : z = 0 := by
    rcases h with h | h
    · have hz : ((a : ℂ) - Complex.I) * z = 0 := by linear_combination h
      apply (mul_eq_zero.mp hz).resolve_left
      intro ha
      have hIm := congrArg Complex.im (sub_eq_zero.mp ha)
      norm_num at hIm
    · have hz : ((a : ℂ) + Complex.I) * z = 0 := by linear_combination h
      apply (mul_eq_zero.mp hz).resolve_left
      intro ha
      have hIm := congrArg Complex.im ha
      norm_num at hIm
  constructor
  · intro w hw
    apply htotal w
    intro i
    apply hscalar (lam i)
    left
    have hh := hw (e i)
    rw [heig i] at hh
    simpa only [Submodule.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal] using hh
  · intro w hw
    apply htotal w
    intro i
    apply hscalar (lam i)
    right
    have hh := hw (e i)
    rw [heig i] at hh
    simpa only [Submodule.coe_smul, inner_smul_left, inner_neg_right, inner_smul_right, Complex.conj_ofReal] using hh

#print axioms solution
