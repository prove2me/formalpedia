-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_colH_strip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:04.744462+00:00
-- url     : https://prove2.me/submissions/28d6ff1c-68d4-4164-b481-f37366b95cbe

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_lt_colH_iff


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
theorem _root_.solution {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (c : ℤ) : colH kap c = colH lam c ∨ colH kap c = colH lam c + 1 := by
  have h1 : colH lam c ≤ colH kap c := by
    by_contra hcon
    have hlt : colH kap c < n := lt_of_lt_of_le (not_le.1 hcon) (colH_le lam c)
    have h2 := (qb_lt_colH_iff hl c ⟨colH kap c, hlt⟩).1 (not_le.1 hcon)
    have h3 := (qb_lt_colH_iff hk c ⟨colH kap c, hlt⟩).2 (h2.trans (hs.1 _))
    exact lt_irrefl _ h3
  have h2 : colH kap c ≤ colH lam c + 1 := by
    by_contra hcon
    have hlt : colH lam c + 1 < n := lt_of_lt_of_le (not_le.1 hcon) (colH_le kap c)
    have h2 := (qb_lt_colH_iff hk c ⟨colH lam c + 1, hlt⟩).1 (not_le.1 hcon)
    have h3 := hs.2.1 ⟨colH lam c, by omega⟩ hlt
    have h4 := (qb_lt_colH_iff hl c ⟨colH lam c, by omega⟩).2 (h2.trans h3)
    exact lt_irrefl _ h4
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
