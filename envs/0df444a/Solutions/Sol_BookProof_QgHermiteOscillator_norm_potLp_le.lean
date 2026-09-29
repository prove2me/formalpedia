-- Prove2me | solution 1 for BookProof.QgHermiteOscillator.norm_potLp_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:42:15.190996+00:00
-- url     : https://prove2.me/submissions/7f489469-b45f-4aaf-992a-c6924bbccc24

-- Generated from ChapterQgHermiteOscillatorEsa.lean — solution of BookProof.QgHermiteOscillator.norm_potLp_le
import Mathlib
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Theorems.Thm_BookProof_QgHermiteFriedrichs_potLp_coeFn
open BookProof.QgHermiteOscillator












open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ι : Type*} {D : Submodule ℂ F}





variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {B : Vd d → ℝ} {M : ℝ} (hBc : Continuous B) (hBb : ExpBounded B)
    (hM : ∀ x, |B x| ≤ M) (p : MvPolynomial (Fin d) ℂ) :
    ‖potLp B hBc hBb p‖ ≤ M * ‖pgLp p‖ := by

  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hle : ‖potLp B hBc hBb p‖ ≤ ‖((M : ℝ) : ℂ) • pgLp p‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [potLp_coeFn B hBc hBb p, Lp.coeFn_smul ((M : ℝ) : ℂ) (pgLp p),
      pgLp_coeFn p] with x hx hy hz
    rw [hx, hy, Pi.smul_apply, hz]
    simp only [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((hM x).trans (le_abs_self M)) (norm_nonneg _)
  refine hle.trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
