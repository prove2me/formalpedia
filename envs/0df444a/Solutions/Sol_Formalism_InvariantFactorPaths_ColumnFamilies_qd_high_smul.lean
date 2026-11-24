-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_high_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:24.30562+00:00
-- url     : https://prove2.me/submissions/61811f5c-32af-475e-9b6d-70c517de96a8

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) (c : R) {x : M.ι → R}
    (hx : IsHighest M R mu x) : IsHighest M R mu (c • x) :=
  ⟨by rw [Matrix.mulVec_smul, hx.1], fun R' _ _ u h1 h2 => by
    have e : (fun i => algebraMap R R' ((c • x) i)) = algebraMap R R' c • fun i => algebraMap R R' (x i) := by
      funext i; simp
    rw [e, Matrix.mulVec_smul, hx.2 R' u h1 h2]⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
