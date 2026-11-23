-- Prove2me | solution 1 for Formalism.REAL.word_action_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:38.281477+00:00
-- url     : https://prove2.me/submissions/f217763c-eadf-4118-9609-0f5a63f88011

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_compact_weight_shift

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
theorem _root_.solution (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : IsWeight F μ x)
    (w : List (Fin n × Fin n)) (hw : ∀ p ∈ w, ε p.1 = ε p.2) :
    IsWeight F (μ + wordWeightShift w) (ew F w x) := by
  induction w with
  | nil => simp only [wordWeightShift, add_zero]; exact hx
  | cons p w ih =>
    have := compact_weight_shift h (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)))
      (hw p List.mem_cons_self)
    have e : μ + wordWeightShift (p :: w) = μ + wordWeightShift w + Pi.single p.1 1 - Pi.single p.2 1 := by
      simp only [wordWeightShift]; abel
    rw [e]; exact this
end Formalism.REAL
