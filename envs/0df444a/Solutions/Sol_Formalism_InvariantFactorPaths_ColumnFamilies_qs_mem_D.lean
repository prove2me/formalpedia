-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_mem_D
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:39.536912+00:00
-- url     : https://prove2.me/submissions/24917c4d-0ee4-4850-9802-908784ca488f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_high
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_low


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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {lam kap : Fin n → ℤ} (hl : Dominant lam) (hk : Dominant kap) (c : ℤ) :
    c ∈ qs_D lam kap ↔ colH kap c = colH lam c + 1 := by
  simp only [qs_D, mem_filter, mem_Ioc, and_iff_right_iff_imp]
  intro h
  constructor
  · by_contra hcon
    have := qs_colH_low hl (not_lt.1 hcon)
    have := colH_le kap c
    omega
  · by_contra hcon
    have := qs_colH_high hk (not_le.1 hcon)
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
