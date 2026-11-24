-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_mem_dualWeyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:53:10.258069+00:00
-- url     : https://prove2.me/submissions/8d42466c-f843-45dc-8f51-0d95971e95d7

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_homog
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_invariant
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
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n ν := by
  rw [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf]
  refine ⟨qh_homog Q ν hQ, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  intro l j hlj
  exact qh_invariant Q ν hQ l j hlj
end Formalism.InvariantFactorPaths.ColumnFamilies
