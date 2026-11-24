-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_eq_of_psum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:13.051566+00:00
-- url     : https://prove2.me/submissions/c5c32d19-3c26-42f5-8ad1-b6a475cef51b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW

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
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {f g : Fin n → ℤ}
    (h : ∀ a : Fin n, ∑ b ∈ univ.filter (· ≤ a), f b = ∑ b ∈ univ.filter (· ≤ a), g b) : f = g := by
  funext a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    have h1 := h a
    have e : (univ.filter (· ≤ a) : Finset (Fin n)) = insert a (univ.filter (· < a)) := by
      ext b; simp [le_iff_eq_or_lt]
    rw [e, sum_insert (by simp), sum_insert (by simp)] at h1
    have h2 : ∑ b ∈ univ.filter (· < a), f b = ∑ b ∈ univ.filter (· < a), g b :=
      sum_congr rfl fun b hb => ih b (by simpa using hb)
    linarith
end Formalism.InvariantFactorPaths.ColumnFamilies
