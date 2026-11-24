-- Prove2me | solution 1 for Formalism.REAL.word_product_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:59.785798+00:00
-- url     : https://prove2.me/submissions/7226e1ff-91e8-4be1-9fe1-3b2d98bcd53b

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (α : Fin (j + 1) → Fin n × Fin n) :
    u1W E α = E (α (Fin.last j)).1 (α (Fin.last j)).2 * u1W E (Fin.init α) := by
  unfold u1W
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  rfl
end Formalism.REAL
