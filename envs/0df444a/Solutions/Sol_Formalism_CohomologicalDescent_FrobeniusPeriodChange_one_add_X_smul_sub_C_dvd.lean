-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.one_add_X_smul_sub_C_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:04:51.159359+00:00
-- url     : https://prove2.me/submissions/18bfcb05-0de9-4900-b959-36be5146c480

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_gamma_mod_q_holds

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
theorem _root_.solution {O : Type} [CommRing O] (lam : O) {n : ℕ}
    (D : Matrix (Fin n) (Fin n) O⟦X⟧) (Th : Matrix (Fin n) (Fin n) O)
    (h : ∀ a b, (X - C lam) ∣ D a b - C (Th a b)) (a b : Fin n) :
    (X - C lam) ∣ (1 + (X : O⟦X⟧) • D) a b - C ((1 + lam • Th) a b) := by
  exact gamma_mod_q_holds O lam n D Th h a b
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
