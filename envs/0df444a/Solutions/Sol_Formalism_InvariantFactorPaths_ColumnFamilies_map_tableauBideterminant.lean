-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.map_tableauBideterminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:28:35.20169+00:00
-- url     : https://prove2.me/submissions/46135b00-2446-4f9d-a388-f2658db328a3

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
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
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (I : TIdx mu) : MvPolynomial.map φ (qa_P R I) = qa_P S I := by
  unfold qa_P
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp
end Formalism.InvariantFactorPaths.ColumnFamilies
