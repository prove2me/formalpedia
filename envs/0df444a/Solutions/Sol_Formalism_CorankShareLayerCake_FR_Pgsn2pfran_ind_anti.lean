-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfran.ind_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:02.512225+00:00
-- url     : https://prove2.me/submissions/b8b6ba12-6f86-4b7a-b0b6-5bb153d65412

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Finset MeasureTheory
open Formalism.CorankShareLayerCake.FR.Pgsn2pfran
namespace Formalism.CorankShareLayerCake.FR.Pgsn2pfran
theorem _root_.solution (c : ℝ) : Antitone (fun τ : ℝ => if τ < c then (1:ℝ) else 0) := by
  intro a b hab
  show (if b < c then (1:ℝ) else 0) ≤ (if a < c then (1:ℝ) else 0)
  by_cases h1 : b < c
  · have h2 : a < c := lt_of_le_of_lt hab h1
    simp [h1, h2]
  · by_cases h2 : a < c <;> simp [h1, h2]
end Formalism.CorankShareLayerCake.FR.Pgsn2pfran
