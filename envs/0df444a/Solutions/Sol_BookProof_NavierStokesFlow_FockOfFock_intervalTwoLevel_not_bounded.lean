-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:24:48.816998+00:00
-- url     : https://prove2.me/submissions/6fcc2aa4-77fd-4468-baf4-f05a177bbf1c

import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_not_bounded
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {K : Type*} [DecidableEq K]
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock in
theorem h44_diag_basis {ι : Type*} [DecidableEq ι] (c : ι → ℝ) (n : ι) :
    ‖lpDiag c (lpBasis n)‖ = |c n| := by
  have h : ((lpDiag c (lpBasis n) : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2)
      = lp.single 2 n (c n : ℂ) := by
    refine lp.ext ?_
    funext i
    change (c i : ℂ) * (lp.single 2 n (1 : ℂ) : ι → ℂ) i = (lp.single 2 n (c n : ℂ) : ι → ℂ) i
    rw [lp.single_apply, lp.single_apply]
    by_cases hi : i = n
    · subst hi; simp
    · simp [hi]
  rw [Submodule.coe_norm, h, lp.norm_single (by norm_num : (0:ENNReal) < 2)]
  simp

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock in
theorem h44_basis_norm {ι : Type*} [DecidableEq ι] (n : ι) : ‖(lpBasis n : lpFiniteModes ι)‖ = 1 := by
  change ‖(lp.single 2 n (1 : ℂ) : lp (fun _ : ι => ℂ) 2)‖ = 1
  rw [lp.norm_single (by norm_num : (0:ENNReal) < 2)]; simp

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock MeasureTheory in
theorem h44_ext_ge (j : ℕ) : (j : ℝ) ≤ symbolOfIntegral volume extField intervalDens j := by
  unfold symbolOfIntegral extField intervalDens
  have e : (fun ξ : ℝ => ξ ^ 2 * Set.indicator (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) (fun _ => (1:ℝ)) ξ)
      = Set.indicator (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) (fun ξ => ξ ^ 2) := by
    funext ξ; by_cases h : ξ ∈ Set.Ioc (j : ℝ) ((j : ℝ) + 1) <;> simp [h]
  rw [e, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    integral_pow]
  nlinarith [sq_nonneg (j : ℝ)]

theorem solution (eps : K → ℝ) :
    ¬ ∃ C : ℝ, ∀ f : FockOfFockDom ℕ K,
      ‖dGamma (intervalTwoLevelSymbol eps) f‖ ≤ C * ‖f‖ := by
  rintro ⟨C, hC⟩
  classical
  obtain ⟨j, hj⟩ := exists_nat_gt C
  let n : Conf (ℕ × Conf K) := Finsupp.single (j, (0 : Conf K)) 1
  have h1 := hC (lpBasis n)
  rw [show dGamma (intervalTwoLevelSymbol eps) (lpBasis n)
      = lpDiag (confEnergy (intervalTwoLevelSymbol eps)) (lpBasis n) from rfl,
    h44_diag_basis, h44_basis_norm, mul_one] at h1
  have hE : confEnergy (intervalTwoLevelSymbol eps) n
      = symbolOfIntegral volume extField intervalDens j := by
    simp [n, FockOfFock.confEnergy, intervalTwoLevelSymbol, Finsupp.support_single]
  rw [hE] at h1
  have := h44_ext_ge j
  have := le_abs_self (symbolOfIntegral volume extField intervalDens j)
  linarith

