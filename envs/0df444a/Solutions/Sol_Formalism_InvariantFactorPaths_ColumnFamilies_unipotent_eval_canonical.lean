-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.unipotent_eval_canonical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:54:00.918824+00:00
-- url     : https://prove2.me/submissions/03d1051c-14d9-415c-893c-4a5541ab969a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_det_unitri
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_minor_unitri
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGL_detU
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
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) (mu : Fin n → ℤ) (K : TIdx mu) :
    evGL u (TMat mu K (canT mu)) = if K = canT mu then 1 else 0 := by
  unfold TMat
  rw [map_mul, map_prod, qd_evGL_detU, qd_det_unitri u h1 h2, one_zpow, Units.val_one, one_mul]
  simp only [qd_minor_unitri u h1 h2]
  split_ifs with hK
  · subst hK
    simp
  · obtain ⟨c, hc⟩ : ∃ c, K c ≠ canT mu c := by
      by_contra hcon
      push Not at hcon
      exact hK (funext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ c) (if_neg hc)
end Formalism.InvariantFactorPaths.ColumnFamilies
