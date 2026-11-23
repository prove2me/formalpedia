-- Prove2me | solution 1 for Formalism.REAL.compactSpan_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:18.374711+00:00
-- url     : https://prove2.me/submissions/d042985f-1f6d-42db-88f9-66d05ef753d1

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin n → Bool) (T : Fin n → Fin n → Module.End ℂ V) (x : V) :
    KStable ε T (kSpan ε T x) := by
  intro a b hab y hy
  simp only [kSpan, Submodule.mem_sInf, Set.mem_setOf_eq] at hy ⊢
  intro S hS
  exact hS.2 a b hab y (hy S hS)
end Formalism.REAL
