-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.gaussInt_coreD_sq_pair
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T09:56:25.105647+00:00
-- url     : https://prove2.me/submissions/645080e9-28ac-4b9b-adca-214b014f1469

-- Generated from ChapterGaussCoreQuadBounds.lean — solution of BookProof.GaussCoreQuadBounds.gaussInt_coreD_sq_pair
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
import Theorems.Thm_BookProof_GaussCoreQuadBounds_coreD_comm
import Theorems.Thm_BookProof_GaussCoreQuadBounds_gaussInt_self
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_coreD
open BookProof.GaussCoreQuadBounds









open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    gaussInt (cpoly (coreD j (coreD j p)) * coreD k (coreD k p))
      = ((‖pgLp (coreD k (coreD j p))‖ ^ 2 : ℝ) : ℂ) := by

  have hcomm : coreD j (coreD k (coreD k p)) = coreD k (coreD k (coreD j p)) := by
    rw [coreD_comm j k (coreD k p), coreD_comm j k p]
  have h1 : gaussInt (cpoly (coreD j (coreD j p)) * coreD k (coreD k p))
      = -gaussInt (cpoly (coreD j p) * coreD j (coreD k (coreD k p))) :=
    gaussInt_coreD j (coreD j p) (coreD k (coreD k p))
  have h2 : gaussInt (cpoly (coreD k (coreD j p)) * coreD k (coreD j p))
      = -gaussInt (cpoly (coreD j p) * coreD k (coreD k (coreD j p))) :=
    gaussInt_coreD k (coreD j p) (coreD k (coreD j p))
  rw [h1, hcomm, ← h2, gaussInt_self]
