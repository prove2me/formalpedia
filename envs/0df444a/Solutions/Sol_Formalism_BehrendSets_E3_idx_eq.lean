-- Prove2me | solution 1 for Formalism.BehrendSets.E3.idx_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:34.168834+00:00
-- url     : https://prove2.me/submissions/eb18e498-3ed6-4473-9a6c-c381a2e63aa7

import Definitions.Def_Formalism_BehrendSets_StatementE
import Mathlib
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MulAbsSubLt
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_SpaceFreeOfBehrendFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.E3
namespace Formalism.BehrendSets.E3
theorem _root_.solution {n Lw : ℕ} {h u t : ZMod n} (hord : Lw < addOrderOf h) {y : ℕ} {a b : ℤ}
    (hab : |a - b| ≤ (Lw : ℤ)) (ea : ((y : ℕ) : ZMod n) + u = t + a • h)
    (eb : ((y : ℕ) : ZMod n) + u = t + b • h) : a = b := by
  have hsm : a • h = b • h := by
    have : t + a • h = t + b • h := by rw [← ea, ← eb]
    exact add_left_cancel this
  have hz : (a - b) • h = 0 := by rw [sub_zsmul, hsm]; abel
  have hd : ((addOrderOf h : ℕ) : ℤ) ∣ (a - b) := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
  have hlt : |a - b| < ((addOrderOf h : ℕ) : ℤ) := by
    have : (Lw : ℤ) < ((addOrderOf h : ℕ) : ℤ) := by exact_mod_cast hord
    linarith
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd hlt)
end Formalism.BehrendSets.E3
