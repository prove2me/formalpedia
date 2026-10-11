-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:06.478455+00:00
-- url     : https://prove2.me/submissions/7f5cfbb5-7fd4-4008-9079-7615075e46e7

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_differentiable
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_deriv
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_integrable
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_sub
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_const_mul
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_coord_mul
import Theorems.Thm_BookProof_WeakSecondDeriv_exists_unitTest
import Theorems.Thm_BookProof_WeakSecondDeriv_exists_antideriv
import Theorems.Thm_BookProof_WeakSecondDeriv_integral_eq_neg_integral_coord_mul_deriv
import Theorems.Thm_BookProof_WeakSecondDeriv_integrable_test_smul
import Theorems.Thm_BookProof_WeakSecondDeriv_ae_eq_const_of_integral_deriv_smul_eq_zero
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {r : ℝ → F}
    (hr : LocallyIntegrable r volume)
    (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv (deriv g) x • r x = 0) :
    ∃ a b : F, r =ᵐ[volume] fun x => x • a + b := by

  obtain ⟨ρ, hρ, hρ1⟩ := exists_unitTest
  set k : F := ∫ x, deriv ρ x • r x with hk
  -- for every test function `ψ`, `∫ ψ' • r = (∫ ψ) • k`
  have key : ∀ ψ : ℝ → ℝ, IsTestFun ψ → ∫ x, deriv ψ x • r x = (∫ x, ψ x) • k := by
    intro ψ hψ
    set I := ∫ x, ψ x with hI
    have hIρ : IsTestFun (fun x => I * ρ x) := hρ.const_mul I
    have hχ : IsTestFun (fun x => ψ x - I * ρ x) := hψ.sub hIρ
    have hχ0 : ∫ x, (ψ x - I * ρ x) = 0 := by
      rw [integral_sub hψ.integrable hIρ.integrable, MeasureTheory.integral_const_mul, hρ1]
      simp [hI]
    obtain ⟨G, hG, hdG⟩ := exists_antideriv hχ hχ0
    have h1 := h G hG
    rw [hdG] at h1
    have hdχ : deriv (fun x => ψ x - I * ρ x) = fun x => deriv ψ x - I * deriv ρ x := by
      funext x
      have h2 : HasDerivAt (fun x => ψ x - I * ρ x)
          (deriv ψ x - I * deriv ρ x) x :=
        ((hψ.differentiable x).hasDerivAt).sub
          (((hρ.differentiable x).hasDerivAt).const_mul I)
      exact h2.deriv
    rw [hdχ] at h1
    have hint2 : Integrable (fun x => I • (deriv ρ x • r x)) volume :=
      (integrable_test_smul hρ.deriv hr).smul I
    have h2 : ∫ x, (deriv ψ x - I * deriv ρ x) • r x
        = (∫ x, deriv ψ x • r x) - I • k := by
      have he : ∀ x, (deriv ψ x - I * deriv ρ x) • r x
          = deriv ψ x • r x - I • (deriv ρ x • r x) := by
        intro x; rw [sub_smul, smul_smul]
      simp_rw [he]
      rw [integral_sub (integrable_test_smul hψ.deriv hr) hint2, MeasureTheory.integral_smul]
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  -- hence `r + x • k` is orthogonal to every derivative, so it is a.e. constant
  set s : ℝ → F := fun x => r x + x • k with hs
  have hsloc : LocallyIntegrable s volume := by
    refine hr.add ?_
    exact (continuous_id.smul continuous_const).locallyIntegrable
  have hzero : ∀ ψ : ℝ → ℝ, IsTestFun ψ → ∫ x, deriv ψ x • s x = 0 := by
    intro ψ hψ
    have he : ∀ x, deriv ψ x • s x = deriv ψ x • r x + (x * deriv ψ x) • k := by
      intro x
      rw [hs]
      simp only [smul_add, smul_smul]
      rw [mul_comm]
    simp_rw [he]
    rw [integral_add (integrable_test_smul hψ.deriv hr)
      ((hψ.deriv.coord_mul.integrable).smul_const k), _root_.integral_smul_const, key ψ hψ,
      integral_eq_neg_integral_coord_mul_deriv hψ]
    module
  obtain ⟨b, hb⟩ := ae_eq_const_of_integral_deriv_smul_eq_zero hsloc hzero
  refine ⟨-k, b, ?_⟩
  filter_upwards [hb] with x hx
  have : r x + x • k = b := hx
  rw [smul_neg, ← this]
  abel
