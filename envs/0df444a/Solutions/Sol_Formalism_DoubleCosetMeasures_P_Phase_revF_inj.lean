-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.revF_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:00.798322+00:00
-- url     : https://prove2.me/submissions/411a7534-5f2a-41c6-bca2-b44e270e8feb

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution (s : List ℕ) {a c : Fin s.sum} (h : revF s a = revF s c) : a = c := by
  calc a = revF s (revF s a) := (revF_revF s a).symm
    _ = revF s (revF s c) := by rw [h]
    _ = c := revF_revF s c
end Formalism.DoubleCosetMeasures.P.Phase
