-- Prove2me | solution 1 for Formalism.REAL.drop_ofFn_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:32.491802+00:00
-- url     : https://prove2.me/submissions/7602904b-cb24-4133-b6fa-417b965ca2b9

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {α : Type*} {t : ℕ} (f g : Fin t → α) (i : ℕ)
    (h : ∀ k : Fin t, i ≤ (k : ℕ) → f k = g k) :
    (List.ofFn f).drop i = (List.ofFn g).drop i := by
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    simp only [List.getElem_drop, List.getElem_ofFn]
    apply h
    exact Nat.le_add_right _ _
end Formalism.REAL
