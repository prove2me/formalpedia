-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_minor_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:23.389256+00:00
-- url     : https://prove2.me/submissions/c2683cf3-593e-46b3-a4ad-48d0b4a0c28c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_ext_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_emb_map
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_emb_insert
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_det_cast
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_det_snoc

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
variable {m : ℕ} {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hb : IsBlock h g1 t) (e : Prop) [Decidable e] (K' S : Finset (Fin m)) {k k' : ℕ}
    (hK' : K'.card = k') (hS' : S.card = k') (hK : (qr_ext e K').card = k) (hS : (qr_ext e S).card = k) :
    (h.val.submatrix ((qr_ext e K').orderEmbOfFin hK) ((qr_ext e S).orderEmbOfFin hS)).det =
      (if e then (t : R) else 1) * (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
  by_cases he : e
  · have hk : k = k' + 1 := by rw [← hK, qr_ext_card, hK', if_pos he]
    subst hk
    have key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k' + 1) (hB : B.card = k' + 1),
        A = insert (Fin.last m) (K'.map Fin.castSuccEmb) → B = insert (Fin.last m) (S.map Fin.castSuccEmb) →
        (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det =
          (t : R) * (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
      intro A B hA hB eA eB
      subst eA eB
      rw [qr_emb_insert K' hK', qr_emb_insert S hS', qr_det_snoc hb]
    rw [if_pos he]
    exact key _ _ hK hS (by rw [qr_ext, if_pos he]) (by rw [qr_ext, if_pos he])
  · have hk : k = k' := by rw [← hK, qr_ext_card, hK', if_neg he]; rfl
    subst hk
    have key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k) (hB : B.card = k),
        A = K'.map Fin.castSuccEmb → B = S.map Fin.castSuccEmb →
        (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det =
          (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
      intro A B hA hB eA eB
      subst eA eB
      rw [qr_emb_map K' hK', qr_emb_map S hS', qr_det_cast hb]
    rw [if_neg he, one_mul]
    exact key _ _ hK hS (by rw [qr_ext, if_neg he]) (by rw [qr_ext, if_neg he])
end Formalism.InvariantFactorPaths.ColumnFamilies
