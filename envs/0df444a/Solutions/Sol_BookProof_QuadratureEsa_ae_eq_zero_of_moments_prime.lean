-- Prove2me | solution 1 for BookProof.QuadratureEsa.ae_eq_zero_of_moments_prime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:40:18.789353+00:00
-- url     : https://prove2.me/submissions/36938564-519c-4486-8d8e-62f7c46bbb94

-- Generated from ChapterQuadratureEsa.lean — theorem BookProof.QuadratureEsa.ae_eq_zero_of_moments'
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteCore
open BookProof.HermiteProductCore
open BookProof.QuadratureEsa



open MeasureTheory MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.YangMillsHermite
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

variable {d : ℕ}
theorem solution {v : Vd d → ℂ}
    (hmeas : AEStronglyMeasurable v (volume : Measure (Vd d)))
    (hexp : ∀ c : ℝ, Integrable (fun x : Vd d => Real.exp (c * ‖x‖) * ‖v x‖))
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ,
      ∫ x : Vd d, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p * v x = 0) :
    ∀ᵐ x : Vd d, v x = 0 := by
  exact BookProof.QuadratureEsa.ae_eq_zero_of_moments' hmeas hexp hmom
