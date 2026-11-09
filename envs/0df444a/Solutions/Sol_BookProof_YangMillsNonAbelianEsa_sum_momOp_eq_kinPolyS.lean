-- Prove2me | solution 1 for BookProof.YangMillsNonAbelianEsa.sum_momOp_eq_kinPolyS
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:30:17.688577+00:00
-- url     : https://prove2.me/submissions/a8b4a2f3-a92f-424f-82c8-6f9781747fba

-- Generated from ChapterYangMillsNonAbelianEsa.lean — solution of BookProof.YangMillsNonAbelianEsa.sum_momOp_eq_kinPolyS
import Mathlib
import Definitions.Def_ChapterYangMillsNonAbelianEsa
import Theorems.Thm_BookProof_YangMillsNonAbelianEsa_momOp_momOp_d
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterDegKatoEsa
import Definitions.Def_ChapterHermiteGraphApprox
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgHermiteFriedrichs
open BookProof.YangMillsNonAbelianEsa




open MeasureTheory MvPolynomial
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.DegSchrodinger BookProof.DegKatoEsa BookProof.HermiteGraphApprox
open BookProof.TensorCore BookProof.DirectSumEsa BookProof.SecondQuantizationCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QgHermiteFriedrichs

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}
variable {d : ℕ}
variable {d k r : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {idx : Fin k → Fin d} (hidx : Function.Injective idx)
    (p : MvPolynomial (Fin d) ℂ) :
    (∑ m : Fin k, momOp (idx m) (momOp (idx m) p)) = kinPolyS (Finset.image idx Finset.univ) p := by

  have h : ∀ m : Fin k, momOp (idx m) (momOp (idx m) p)
      = -coreD (idx m) (coreD (idx m) p) := fun m => momOp_momOp_d _ p
  rw [Finset.sum_congr rfl fun m _ => h m, kinPolyS,
    Finset.sum_image (fun a _ b _ hab => hidx hab)]
  simp only [Finset.sum_neg_distrib]
