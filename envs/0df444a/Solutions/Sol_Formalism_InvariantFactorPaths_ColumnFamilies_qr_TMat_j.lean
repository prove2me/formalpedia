-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_TMat_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:50:25.034434+00:00
-- url     : https://prove2.me/submissions/bc35f8b4-9728-40e6-b6af-c9ba3ab1dfab

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_dU_block
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_prod_G
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_card_C
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_dU_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_detU_zpow
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_minorC
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_lam_last_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_lastIdx
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_minor_ext


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
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ} {R : Type} [CommRing R]
  {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hb : IsBlock h g1 t) (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (K' I' : TIdx nu) :
    evGL h (TMat lam (qr_j hi K') (qr_j hi I')) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) * evGL g1 (TMat nu K' I') := by
  simp only [TMat, map_mul, map_prod, qc_evGL_detU_zpow, qc_evGL_minorC]
  have h1 : ∀ c : ↥(TCols lam),
      (h.val.submatrix ((qr_j hi K' c).1.orderEmbOfFin (qr_j hi K' c).2)
        ((qr_j hi I' c).1.orderEmbOfFin (qr_j hi I' c).2)).det =
      (if colH lam c = colH nu c + 1 then (t : R) else 1) * qr_G g1 K' I' c := fun c =>
    qr_minor_ext hb _ _ _ (qr_base K' c).2 (qr_base I' c).2 _ _
  rw [Finset.prod_congr rfl (fun c _ => h1 c), Finset.prod_mul_distrib,
    Finset.prod_coe_sort (TCols lam) (fun c => if colH lam c = colH nu c + 1 then (t : R) else 1),
    Finset.prod_coe_sort (TCols lam) (fun c => qr_G g1 K' I' c), qr_prod_G hn hi, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const_one, mul_one, qr_dU_block hb, qr_lastIdx]
  have hC := qr_card_C hl hn hi
  set N := ((TCols lam).filter fun c => colH lam c = colH nu c + 1).card
  set P := (nu (lastIdx m) - lam (Fin.last m)).toNat with hP
  have hP' : (P : ℤ) = nu (lastIdx m) - lam (Fin.last m) :=
    Int.toNat_of_nonneg (sub_nonneg.2 (qr_lam_last_le hi))
  have e1 : t ^ (∑ a, lam a - ∑ a, nu a) = t ^ lam (Fin.last m) * t ^ N := by
    rw [← zpow_natCast, ← zpow_add, hC]; congr 1; ring
  have e2 : qc_dU g1 ^ nu (lastIdx m) = qc_dU g1 ^ lam (Fin.last m) * qc_dU g1 ^ P := by
    rw [← zpow_natCast, ← zpow_add, hP']; congr 1; ring
  rw [e1, e2, mul_zpow]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, qc_dU_coe]
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
