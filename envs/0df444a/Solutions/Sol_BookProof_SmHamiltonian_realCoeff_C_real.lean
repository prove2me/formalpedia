-- Prove2me | solution 1 for BookProof.SmHamiltonian.realCoeff_C_real
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:13.256182+00:00
-- url     : https://prove2.me/submissions/a814f196-60f6-4aa0-a656-ab0577f04217

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.realCoeff_C_real
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Theorems.Thm_BookProof_YangMillsHermite_starP_C
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsHermite
open BookProof.SmHamiltonian




open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {d : ℕ} (t : ℝ) :
    RealCoeff (C ((t : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ) := by

  change starP (C ((t : ℝ) : ℂ)) = C ((t : ℝ) : ℂ)
  rw [starP_C, Complex.conj_ofReal]
