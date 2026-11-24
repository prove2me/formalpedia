-- Prove2me | solution 1 for Formalism.REAL.compact_span_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:34:42.53571+00:00
-- url     : https://prove2.me/submissions/fb7449c5-729a-49ed-a8c6-36dec955b1d0

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_compact_span_le_of_stable

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
    {F : Fin n → Fin n → Module.End ℂ W} (M : Submodule ℂ W) : kSpan ε F 0 ≤ M := by
  refine le_trans (compact_span_le_of_stable (S := ⊥) ?_ (Submodule.zero_mem _)) bot_le
  intro a b _ x hx
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]
end Formalism.REAL
