-- Prove2me | solution 1 for BookProof.NsOuterFock.nsOuterHam_esa_core
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:02:05.217872+00:00
-- url     : https://prove2.me/submissions/30469e2b-4245-46e8-be6b-0afc0b045da3

import Definitions.Def_ChapterNsOuterFockFarisLavine
import Definitions.Def_ChapterSqSumOuterFamily

open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.SqSumOuterFamily
open BookProof.NsOuterFock

noncomputable section

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)
variable {bv nu lam mu gg}
variable {B : ℝ} (hB : 0 ≤ B) (hbv : ∀ j, |bv j| ≤ B) (hnu : |nu| ≤ B) (hlam : |lam| ≤ B)
  (hmu : |mu| ≤ B) (hgg : |gg| ≤ B)

theorem solution :
    EssentiallySelfAdjointOn (outerCore (nsFamily hB hbv hnu hlam hmu hgg).dim)
      (nsFamily hB hbv hnu hlam hmu hgg).outerHam := by
  exact (nsFamily hB hbv hnu hlam hmu hgg).outerHam_esa
