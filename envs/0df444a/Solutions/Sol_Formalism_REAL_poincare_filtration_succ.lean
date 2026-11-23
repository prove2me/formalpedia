-- Prove2me | solution 1 for Formalism.REAL.poincare_filtration_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:49.93703+00:00
-- url     : https://prove2.me/submissions/f6da4da0-14db-4f19-ae7a-b33316e258be

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_pfil_monotone_in_length
import Theorems.Thm_Formalism_REAL_noncompact_generator_raises_pfil
import Theorems.Thm_Formalism_REAL_pfil_compact_stable

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
theorem _root_.solution (hE : GlRel E) (j : ℕ) (a b : Fin n) :
    ∀ x ∈ pfil ε E u j, E a b x ∈ pfil ε E u (j + 1) := by
  intro x hx
  by_cases hab : ε a = ε b
  · exact pfil_monotone_in_length ε E u (Nat.le_succ j) (pfil_compact_stable ε E u hE j a b hab x hx)
  · exact noncompact_generator_raises_pfil ε E u j a b hab x hx
end Formalism.REAL
