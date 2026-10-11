-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.moments_of_monomial_moments
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:21:00.39698+00:00
-- url     : https://prove2.me/submissions/06761a24-6fc4-44f0-a729-23bfdf17a89f

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.moments_of_monomial_moments
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_ScalaronHermiteEsa_integrable_pgFun_mul_of_gaussExpDecay
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ScalaronHermiteEsa




open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {u : Vd d → ℂ} (hu : GaussExpDecay u)
    (hmon : ∀ a : Fin d →₀ ℕ, ∫ x : Vd d, pgFun (monomial a (1 : ℂ)) x * u x = 0)
    (p : MvPolynomial (Fin d) ℂ) : ∫ x : Vd d, pgFun p x * u x = 0 := by

  have hsum : p = ∑ v ∈ p.support, (monomial v) (MvPolynomial.coeff v p) :=
    (MvPolynomial.support_sum_monomial_coeff p).symm
  have hpt : ∀ x : Vd d, pgFun p x * u x
      = ∑ v ∈ p.support, MvPolynomial.coeff v p * (pgFun (monomial v (1 : ℂ)) x * u x) := by
    intro x
    rw [pgFun]
    nth_rewrite 1 [hsum]
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [pgFun, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    ring
  simp_rw [hpt]
  rw [integral_finset_sum _ (fun v _ =>
    (integrable_pgFun_mul_of_gaussExpDecay hu (monomial v (1 : ℂ))).const_mul _)]
  simp [integral_const_mul, hmon]
