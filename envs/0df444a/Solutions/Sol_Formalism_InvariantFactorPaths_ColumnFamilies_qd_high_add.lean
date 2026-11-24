-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_high_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:22.242545+00:00
-- url     : https://prove2.me/submissions/83893f55-5b3e-471c-8676-b9a5fac49d64

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
theorem _root_.solution (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) {x y : M.ι → R}
    (hx : IsHighest M R mu x) (hy : IsHighest M R mu y) : IsHighest M R mu (x + y) :=
  ⟨by rw [Matrix.mulVec_add, hx.1, hy.1], fun R' _ _ u h1 h2 => by
    have e : (fun i => algebraMap R R' ((x + y) i)) =
        (fun i => algebraMap R R' (x i)) + fun i => algebraMap R R' (y i) := by funext i; simp
    rw [e, Matrix.mulVec_add, hx.2 R' u h1 h2, hy.2 R' u h1 h2]⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
