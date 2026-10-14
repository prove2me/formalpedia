-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.Msel_idxA
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:10:13.762501+00:00
-- url     : https://prove2.me/submissions/32a28c2a-67f4-421d-b2c1-f7c0abd34e5b

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.Msel_idxA
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_idxA_lt
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

set_option maxHeartbeats 1000000 in
theorem solution (M₁ M₂ : ℕ) (j : Fin 3) (a : Fin 8) : Msel M₁ M₂ (idxA j a) = M₁ := if_pos (idxA_lt j a)
