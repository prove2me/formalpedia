-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:25:06.714399+00:00
-- url     : https://prove2.me/submissions/31be0c5e-cfcb-4022-93e0-f94277398920

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_blockVec_bilH_apply
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ : J → ℝ) (hunb : ∀ C : ℝ, ∃ j, C < κ j) (C : ℝ) :
    ∃ x : lpFiniteModes (ℕ × J),
      ‖((x : lpFiniteModes (ℕ × J)) : L2I (ℕ × J))‖ = 1 ∧ C < ‖bilH κ x‖ := by

  classical
  obtain ⟨j, hj⟩ := hunb (2 * |C| + 2)
  have hκj : 0 ≤ κ j := by
    have : (0 : ℝ) ≤ 2 * |C| + 2 := by positivity
    linarith
  refine ⟨⟨lp.single 2 ((0 : ℕ), j) (1 : ℂ), lpSingle_mem_lpFiniteModes _ _⟩, ?_, ?_⟩
  · simp
  · set x : lpFiniteModes (ℕ × J) :=
      ⟨lp.single 2 ((0 : ℕ), j) (1 : ℂ), lpSingle_mem_lpFiniteModes _ _⟩ with hxdef
    have hX : ∀ n : ℕ, ((x : L2I (ℕ × J)) : ℕ × J → ℂ) (n, j) = if n = 0 then 1 else 0 := by
      intro n
      simp [hxdef, lp.single_apply, Pi.single_apply, Prod.ext_iff]
    have hcoord : ((bilH κ x : L2I (ℕ × J)) : ℕ × J → ℂ) (2, j)
        = Complex.I * ((amp (κ j) 0 : ℝ) : ℂ) := by
      rw [blockVec_bilH_apply]
      simp [hFun, shift2, hX]
    have hb : ‖((bilH κ x : L2I (ℕ × J)) : ℕ × J → ℂ) (2, j)‖ ≤ ‖(bilH κ x : L2I (ℕ × J))‖ :=
      lp.norm_apply_le_norm (by norm_num) _ _
    rw [hcoord] at hb
    have hnv : ‖Complex.I * ((amp (κ j) 0 : ℝ) : ℂ)‖ = amp (κ j) 0 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (amp_nonneg hκj 0)]
    rw [hnv] at hb
    have hs : (1 : ℝ) ≤ Real.sqrt (((0 : ℕ) + 1) * ((0 : ℕ) + 2)) := by
      have h2 : (((0 : ℕ) : ℝ) + 1) * (((0 : ℕ) : ℝ) + 2) = 2 := by norm_num
      rw [show ((((0 : ℕ) : ℝ) + 1) * (((0 : ℕ) : ℝ) + 2)) = 2 from h2]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hamp : κ j / 2 ≤ amp (κ j) 0 := by
      have := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ κ j / 2)
      simpa [amp] using this
    have hC : C ≤ |C| := le_abs_self C
    linarith
