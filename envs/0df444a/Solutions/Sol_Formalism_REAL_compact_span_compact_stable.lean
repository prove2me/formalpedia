-- Prove2me | solution 1 for Formalism.REAL.compact_span_compact_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:00.098952+00:00
-- url     : https://prove2.me/submissions/43807811-48fd-410f-8669-ad75bb6b2e4f

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil

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
theorem _root_.solution : KStable ε E (kSpan ε E u) := by
  intro a b hab x hx
  unfold kSpan at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 a b hab x (hx S hS)
end Formalism.REAL
