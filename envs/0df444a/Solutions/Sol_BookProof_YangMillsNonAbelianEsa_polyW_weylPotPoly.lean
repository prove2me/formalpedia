-- Prove2me | solution 1 for BookProof.YangMillsNonAbelianEsa.polyW_weylPotPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:08:04.70333+00:00
-- url     : https://prove2.me/submissions/1d4a9a83-842b-4cf6-b7df-ccff871073a2

-- Generated from ChapterYangMillsNonAbelianEsa.lean — solution of BookProof.YangMillsNonAbelianEsa.polyW_weylPotPoly
import Mathlib
import Definitions.Def_ChapterYangMillsNonAbelianEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterDegKatoEsa
import Definitions.Def_ChapterHermiteGraphApprox
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsNonAbelianEsa




open MeasureTheory MvPolynomial
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.DegSchrodinger BookProof.DegKatoEsa BookProof.HermiteGraphApprox
open BookProof.TensorCore BookProof.DirectSumEsa BookProof.SecondQuantizationCore
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}
variable {d : ℕ}
variable {d k r : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j))
    (x : Vd d) : polyW (weylPotPoly Φ) x = (∑ j : Fin r, (polyW (Φ j) x) ^ 2) + 1 := by

  have hphi : ∀ j : Fin r, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (Φ j)
      = ((polyW (Φ j) x : ℝ) : ℂ) :=
    fun j => (polyW_ofReal (hΦ j) x).symm
  have key : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (weylPotPoly Φ)
      = (∑ j : Fin r, ((polyW (Φ j) x : ℝ) : ℂ) ^ 2) + ((1 : ℝ) : ℂ) := by
    simp only [weylPotPoly, map_add, map_sum, map_mul, MvPolynomial.eval_C, hphi, sq]
  have hcast : (∑ j : Fin r, ((polyW (Φ j) x : ℝ) : ℂ) ^ 2) + ((1 : ℝ) : ℂ)
      = (((∑ j : Fin r, (polyW (Φ j) x) ^ 2) + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [polyW, key, hcast, Complex.ofReal_re]
