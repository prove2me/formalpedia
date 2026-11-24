-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamma_mod_q_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:56:43.993391+00:00
-- url     : https://prove2.me/submissions/7f09f997-a1c5-4d47-8148-17ee1910e355

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : GammaModQ := by
  intro O _ lam n D Th h a b
  obtain ⟨q, hq⟩ := h a b
  refine ⟨X * q + C (Th a b), ?_⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b = C ((1 : Matrix (Fin n) (Fin n) O) a b) := by
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h1, map_add, map_mul]
  linear_combination X * hq
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
