-- Prove2me | solution 1 for Formalism.REAL.take_ofFn_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:34.634739+00:00
-- url     : https://prove2.me/submissions/e51b2c0d-6fa4-4a6b-8058-025ec75f4b22

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
    (h : ∀ k : Fin t, (k : ℕ) < i → f k = g k) :
    (List.ofFn f).take i = (List.ofFn g).take i := by
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h
    simp only [List.length_take, List.length_ofFn] at hk₁
    show k < i
    omega
end Formalism.REAL
