-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.Adapted.coefA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:47:57.438115+00:00
-- url     : https://prove2.me/submissions/8e768ed2-938d-4fcc-88aa-792e924b401d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.Adapted
open Formalism.REAL
namespace Formalism.FourierDecayAlt.Q.Adapted
theorem _root_.solution {n : ℕ} (j j' : Fin (n + 2)) (h : j < j') :
    (Pi.single 0 1 : Fin (n + 2) → ℂ) j * (Pi.single 1 1 : Fin (n + 2) → ℂ) j' -
      (Pi.single 0 1 : Fin (n + 2) → ℂ) j' * (Pi.single 1 1 : Fin (n + 2) → ℂ) j =
      if j = 0 ∧ j' = 1 then 1 else 0 := by
  have hC : j' ≠ 0 := by
    rintro rfl
    simp [Fin.lt_def] at h
  by_cases hA : j = 0 <;> by_cases hB : j' = 1 <;> simp [Pi.single_apply, hA, hB, hC]
end Formalism.FourierDecayAlt.Q.Adapted
