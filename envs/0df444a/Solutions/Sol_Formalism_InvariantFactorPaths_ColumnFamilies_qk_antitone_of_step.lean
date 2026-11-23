-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_antitone_of_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:15.297453+00:00
-- url     : https://prove2.me/submissions/608559c5-ab6b-4e7c-8e06-de0b7de17c4a

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
theorem _root_.solution {n : ℕ} {f : Fin n → ℤ} (h : ∀ a : Fin n, ∀ h : a.1 + 1 < n, f ⟨a.1 + 1, h⟩ ≤ f a) :
    Antitone f := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ m =>
    rw [Fin.antitone_iff_succ_le]
    intro i
    exact h i.castSucc (by simp)
end Formalism.InvariantFactorPaths.ColumnFamilies
