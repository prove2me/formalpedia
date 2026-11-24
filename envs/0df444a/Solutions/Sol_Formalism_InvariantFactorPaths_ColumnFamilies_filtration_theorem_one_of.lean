-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.filtration_theorem_one_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:31.860137+00:00
-- url     : https://prove2.me/submissions/19bd8e8e-20fd-4e5d-b9ce-cb6fb7f26276

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_WindowBoundOddCases
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_vecF_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LemmaA → ColumnFamilyStandardVectorsBasis := by
  intro hA n _ M CF
  refine ⟨?_, fun R _ => qb_basisR hA CF R⟩
  have := qb_basisR hA CF ℤ
  rw [qb_vecF_int] at this
  exact this
end Formalism.InvariantFactorPaths.ColumnFamilies
