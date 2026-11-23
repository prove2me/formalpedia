-- Prove2me | solution 1 for Formalism.REAL.compact_span_le_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:09.450749+00:00
-- url     : https://prove2.me/submissions/4c696a64-6f0c-4d1f-a306-8de350d66b90

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} {S : Submodule ℂ W} {x : W} (hS : KStable ε F S)
    (hx : x ∈ S) : kSpan ε F x ≤ S :=
  sInf_le ⟨hx, hS⟩
end Formalism.REAL
