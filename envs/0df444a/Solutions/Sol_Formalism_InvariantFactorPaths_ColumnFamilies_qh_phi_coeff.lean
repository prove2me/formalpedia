-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_phi_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:42.310958+00:00
-- url     : https://prove2.me/submissions/ba601b9c-b5af-40bc-a567-50077ce14dc0

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_phi_mono
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
theorem _root_.solution (Q : MvPolynomial (Fin n × Fin n) R) (d0 : Fin n × Fin n →₀ ℕ) :
    coeff d0 (coeff (Finsupp.mapDomain Prod.snd d0) (qhPhi R n Q)) = coeff d0 Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [qh_phi_mono]
    by_cases h : d = d0
    · subst h; simp
    · rw [coeff_monomial, coeff_monomial, if_neg h]
      split_ifs
      · rw [coeff_monomial, if_neg h]
      · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, coeff_add, hp, hq]
end Formalism.InvariantFactorPaths.ColumnFamilies
