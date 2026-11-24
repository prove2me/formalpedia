-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:52.394325+00:00
-- url     : https://prove2.me/submissions/5951b5e5-0564-484e-a9b7-7c79664a659d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} {f f' : GLCoord R n} (hf : f ∈ inducedSections R mu) (hf' : f' ∈ inducedSections R mu) :
    f + f' ∈ inducedSections R mu := by
  intro R' _ _ b g hb
  rw [map_add, map_add, add_mul, mul_add, hf R' b g hb, hf' R' b g hb]
end Formalism.InvariantFactorPaths.ColumnFamilies
