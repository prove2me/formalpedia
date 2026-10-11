-- Prove2me | solution 1 for BookProof.SmHamiltonian.RealCoeff.sub_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:02:43.771782+00:00
-- url     : https://prove2.me/submissions/d8f28818-ecbb-4695-97b1-0e3fef91609f

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.RealCoeff.sub'
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Theorems.Thm_BookProof_YangMillsHermite_starP_sub
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
theorem solution {d : ℕ} {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p)
    (hq : RealCoeff q) : RealCoeff (p - q) := by

  change starP (p - q) = p - q
  rw [starP_sub, show starP p = p from hp, show starP q = q from hq]
