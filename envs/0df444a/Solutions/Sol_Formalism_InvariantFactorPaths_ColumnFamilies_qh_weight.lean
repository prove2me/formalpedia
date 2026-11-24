-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:22.961913+00:00
-- url     : https://prove2.me/submissions/cf28eb8c-1137-4455-8201-0bf397b396d5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
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
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (d : Fin n × Fin n →₀ ℕ) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) d = ⇑(Finsupp.mapDomain Prod.snd d) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d1 d2 h1 h2 => rw [map_add, h1, h2, Finsupp.mapDomain_add, Finsupp.coe_add]
  | single v e =>
    rw [Finsupp.weight_single, Finsupp.mapDomain_single]
    funext a
    simp [Formalism.GradedWeylDivisibility.colW, Finsupp.single_apply, Pi.single_apply, eq_comm]
end Formalism.InvariantFactorPaths.ColumnFamilies
