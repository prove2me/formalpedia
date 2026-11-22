-- Prove2me | solution 1 for Formalism.REAL.compact_lie_commutator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:56.482235+00:00
-- url     : https://prove2.me/submissions/54526db5-0f87-4bf7-bdb8-6a87b8e5d04c

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
theorem _root_.solution (h : KRel ε F) {a b c d : Fin n} (hab : ε a = ε b) (hcd : ε c = ε d) (y : V) :
    F a b (F c d y) - F c d (F a b y) =
      (if b = c then F a d y else 0) - (if d = a then F c b y else 0) := by
  have := LinearMap.congr_fun (h a b c d hab hcd) y
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  split_ifs at this ⊢ <;> simpa using this
end Formalism.REAL
