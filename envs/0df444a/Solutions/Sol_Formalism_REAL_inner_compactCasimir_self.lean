-- Prove2me | solution 1 for Formalism.REAL.inner_compactCasimir_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:07.118365+00:00
-- url     : https://prove2.me/submissions/7dd806b1-5e83-494f-861d-6c3b99216ffb

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf

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
namespace Formalism.REAL
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hu : KUnit ε F) (y : V) :
    ⟪y, CasK ε F y⟫_ℂ = ((∑ a, ∑ b, if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) : ℂ) := by
  unfold CasK
  simp only [LinearMap.sum_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [Module.End.mul_apply, ← hu b a h.symm y (F b a y), inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  · simp
end Formalism.REAL
