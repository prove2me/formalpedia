-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sum_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:05.844113+00:00
-- url     : https://prove2.me/submissions/b2dc58d1-0f5c-4cc3-a2fe-a3194c9dd0eb

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge

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
variable {R : Type*} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {N : ℕ} (φ : (Fin (N + 1) → Finset (Fin n)) → R) :
    ∑ D, φ D = ∑ a, ∑ D', φ (Fin.cons a D') := by
  rw [← (Fin.consEquiv (fun _ => Finset (Fin n))).sum_comp, Fintype.sum_prod_type]; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
