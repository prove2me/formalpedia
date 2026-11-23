-- Prove2me | solution 1 for Formalism.REAL.compact_span_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:37.074096+00:00
-- url     : https://prove2.me/submissions/ea19fb65-e9e4-4be9-a176-a63f6c7d4d1f

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  unfold kSpan at *; rw [Submodule.mem_sInf] at *; intro S hS; exact hS.2 a b hab y (hy S hS)
end Formalism.REAL
