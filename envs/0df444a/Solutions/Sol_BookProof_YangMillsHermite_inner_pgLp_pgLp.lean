-- Prove2me | solution 1 for BookProof.YangMillsHermite.inner_pgLp_pgLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:26:08.566377+00:00
-- url     : https://prove2.me/submissions/3a8d4d77-dd38-466b-b243-a0d77aef4712

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.inner_pgLp_pgLp
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_eval_starP
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (starP p * q) := by

  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  have hev : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p * q)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
        * MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q := by
    rw [map_mul, eval_starP]
  rw [hx, hev, pgFun, pgFun, gaussWD_eq_sq]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring
