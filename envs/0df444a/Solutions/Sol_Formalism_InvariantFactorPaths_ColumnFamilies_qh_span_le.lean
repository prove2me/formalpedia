-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_span_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.939605+00:00
-- url     : https://prove2.me/submissions/6eeede60-7f07-4d45-a81e-5280b96bfc52

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_zero_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_add_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_smul_mem

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
theorem _root_.solution {mu : Fin n → ℤ} {S : Set (GLCoord R n)} (hS : S ⊆ inducedSections R mu) :
    (Submodule.span R S : Set (GLCoord R n)) ⊆ inducedSections R mu := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact hS h
  | zero => exact qh_zero_mem mu
  | add x y _ _ hx hy => exact qh_add_mem hx hy
  | smul r x _ hx => exact qh_smul_mem r hx
end Formalism.InvariantFactorPaths.ColumnFamilies
