-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.Msel_idxD
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:17:57.828186+00:00
-- url     : https://prove2.me/submissions/6f085782-878a-4918-ad62-f68a0398c1f4

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.Msel_idxD
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_idxD_ge
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
theorem solution (M₁ M₂ : ℕ) (j k : Fin 3) (a : Fin 8) : Msel M₁ M₂ (idxD j k a) = M₂ := if_neg (by have := idxD_ge j k a; omega)
