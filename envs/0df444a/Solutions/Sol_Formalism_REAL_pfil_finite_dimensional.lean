-- Prove2me | solution 1 for Formalism.REAL.pfil_finite_dimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:44:09.133795+00:00
-- url     : https://prove2.me/submissions/b276986a-ce00-4bc4-9fb9-d83ea1c565b1

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_poincare_filtration_zero
import Theorems.Thm_Formalism_REAL_pfil_succ_le_sup_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution (h0 : FiniteDimensional ℂ (kSpan ε E u)) (j : ℕ) :
    FiniteDimensional ℂ (pfil ε E u j) := by
  induction j with
  | zero => rw [poincare_filtration_zero]; exact h0
  | succ j ih =>
    haveI := ih
    exact Submodule.finiteDimensional_of_le (pfil_succ_le_sup_map ε E u j)
end Formalism.REAL
