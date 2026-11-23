-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_ini_erase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:08.484606+00:00
-- url     : https://prove2.me/submissions/a5d33955-8ea0-4eb9-9f5a-b63c93250d80

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip

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
variable {n : ℕ} [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (h : ℕ) (hh : h < n) : (qs_ini (h + 1) : Finset (Fin n)).erase ⟨h, hh⟩ = qs_ini h := by
  ext x
  simp only [qs_ini, mem_erase, mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff]
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
