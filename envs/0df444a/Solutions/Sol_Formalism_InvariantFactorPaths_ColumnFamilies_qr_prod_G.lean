-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_prod_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:04.206883+00:00
-- url     : https://prove2.me/submissions/e48f1fd7-af40-4d0e-8a1f-4e1577ad8b91

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_G_low
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_G_high
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_base_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_lam_last_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_lastIdx
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_le_last
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_nu_zero_le


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
theorem _root_.solution (hn : Dominant nu) (hi : Interl lam nu) (K' I' : TIdx nu) :
    ∏ c ∈ TCols lam, qr_G g1 K' I' c =
      g1.val.det ^ (nu (lastIdx m) - lam (Fin.last m)).toNat *
        ∏ c : ↥(TCols nu), (g1.val.submatrix ((K' c).1.orderEmbOfFin (K' c).2)
          ((I' c).1.orderEmbOfFin (I' c).2)).det := by
  have h1 := qr_lam_last_le hi
  have h2 : nu (lastIdx m) ≤ nu 0 := qr_le_last hn 0
  have h3 := qr_nu_zero_le hi
  rw [TCols, qr_lastIdx, ← Finset.Ioc_union_Ioc_eq_Ioc h1 (h2.trans h3),
    Finset.prod_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl), ← Finset.Ioc_union_Ioc_eq_Ioc h2 h3,
    Finset.prod_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [Finset.prod_congr rfl (fun c hc => qr_G_low hn K' I' (Finset.mem_Ioc.1 hc).2), Finset.prod_const,
    Int.card_Ioc,
    Finset.prod_congr (s₁ := Finset.Ioc (nu 0) (lam 0)) rfl (fun c hc => qr_G_high hn K' I' (Finset.mem_Ioc.1 hc).1),
    Finset.prod_const_one, mul_one]
  congr 1
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun c _ => ?_
  have e1 := qr_base_mem K' c
  have e2 := qr_base_mem I' c
  rw [qr_G, e1, e2]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
