-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_det_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:23.524953+00:00
-- url     : https://prove2.me/submissions/f8aa1f70-2ae8-4bd7-8c67-f300bee4982a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} (v : Fin n → ℝ) : (Matrix.vandermonde fun i => (C (v i) : ℝ[X])).det = C (qk_D v) := by
  rw [Matrix.det_vandermonde, qk_D]
  simp only [map_prod, map_sub]
end Formalism.InvariantFactorPaths.ColumnFamilies
