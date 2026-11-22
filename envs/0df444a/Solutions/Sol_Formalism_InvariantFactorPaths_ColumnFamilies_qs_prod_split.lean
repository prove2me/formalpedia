-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_prod_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:26.441632+00:00
-- url     : https://prove2.me/submissions/59151a23-fd78-4dff-b54c-1521bfb9bf11

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd

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
theorem _root_.solution (S D : Finset ℤ) (hD : D ⊆ S) (F : ℤ → R) :
    ∏ c ∈ S, F c = (∏ c ∈ S \ D, F c) * ∏ c : ↥D, F c.1 := by
  rw [← Finset.prod_sdiff hD, Finset.prod_coe_sort]
end Formalism.InvariantFactorPaths.ColumnFamilies
