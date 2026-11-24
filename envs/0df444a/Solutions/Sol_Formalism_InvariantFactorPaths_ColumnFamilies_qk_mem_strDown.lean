-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_mem_strDown
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:23.876646+00:00
-- url     : https://prove2.me/submissions/35f2ec0a-dfae-4919-a280-4b7fca57133b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strDown mu b) : HStrip nu mu b := by
  unfold strDown at h
  simp only [mem_filter] at h
  exact h.2
end Formalism.InvariantFactorPaths.ColumnFamilies
