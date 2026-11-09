-- Prove2me | solution 1 for BookProof.ModeQuadratic.mqOp_deficiencyTrivialAt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T14:02:39.046199+00:00
-- url     : https://prove2.me/submissions/0ab55d23-3e67-4ea9-b1d5-8089af6f4e1b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterModeQuadraticEsa.lean — solution of BookProof.ModeQuadratic.mqOp_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Theorems.Thm_BookProof_ModeQuadratic_mqOp_hermiteCore
import Theorems.Thm_BookProof_CarlemanTwoStep_ladder2_eq_zero
import Theorems.Thm_BookProof_HyperbolicQuadratic_hermiteMvLp_total
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ModeQuadratic




open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p q s b b' : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (mqOp p q s b b') z := by

  classical
  intro w hw
  set u : (Fin d →₀ ℕ) → ℂ := fun a => (inner ℂ (hermiteMvLp (d := d) a) w : ℂ) with hu
  have hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ ‖w‖ ^ 2 := fun F =>
    Orthonormal.sum_inner_products_le (𝕜 := ℂ) w (orthonormal_hermiteMvLp (d := d))
  have hrec : LadderRec2 u (mqSymbol p q) (foAmp b b') (mqAmp p q s) z := by
    intro a
    have h := hw (hermiteCore a)
    rw [mqOp_hermiteCore p q s b b' a, inner_add_left, inner_add_left, inner_smul_left,
      Complex.conj_ofReal, sum_inner, sum_inner] at h
    rw [hermiteCore_coe] at h
    have hq : ∀ i : Fin d,
        (inner ℂ (((mqAmp p q s i * ((rc2 a i : ℝ) : ℂ))
              • hermiteMvLp (d := d) (a + Finsupp.single i 2)
            + ((starRingEnd ℂ) (mqAmp p q s i) * ((lc2 a i : ℝ) : ℂ))
              • hermiteMvLp (d := d) (a - Finsupp.single i 2))) w : ℂ)
        = (starRingEnd ℂ) (mqAmp p q s i) * ((rc2 a i : ℝ) : ℂ)
            * u (a + Finsupp.single i 2)
          + mqAmp p q s i * ((lc2 a i : ℝ) : ℂ) * u (a - Finsupp.single i 2) := by
      intro i
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, hu]
    have hf : ∀ i : Fin d,
        (inner ℂ (((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ))
              • hermiteMvLp (d := d) (a + Finsupp.single i 1)
            + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ))
              • hermiteMvLp (d := d) (a - Finsupp.single i 1))) w : ℂ)
        = (starRingEnd ℂ) (foAmp b b' i) * ((rc1 a i : ℝ) : ℂ) * u (a + Finsupp.single i 1)
          + foAmp b b' i * ((lc1 a i : ℝ) : ℂ) * u (a - Finsupp.single i 1) := by
      intro i
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, hu, rc1, lc1]
    rw [Finset.sum_congr rfl (fun i _ => hq i), Finset.sum_congr rfl (fun i _ => hf i)] at h
    linear_combination h
  have hzero : ∀ a, u a = 0 := ladder2_eq_zero hz hbes hrec
  exact hermiteMvLp_total w fun a => hzero a
