-- Prove2me | solution 1 for Formalism.REAL.isCompactInvariant_compactSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:16.92149+00:00
-- url     : https://prove2.me/submissions/8ba4e701-7b74-456b-a97d-892da316e933

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan

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
  rw [kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b hab y (hy S hS)
end Formalism.REAL
