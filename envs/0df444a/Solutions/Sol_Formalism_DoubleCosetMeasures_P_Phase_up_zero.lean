-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.up_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:01.72375+00:00
-- url     : https://prove2.me/submissions/51969ffb-2944-412c-8940-033f5f96af7b

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution {n : ℕ} {y : Matrix (Fin n) (Fin n) K} (hy : IsUpUni y) {i j : Fin n}
    (h : j < i) : y i j = 0 := by
  first
  | exact hy.1 h
  | (unfold IsUpUni at hy; done)
end Formalism.DoubleCosetMeasures.P.Phase
