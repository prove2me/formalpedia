-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_card_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:44:32.281829+00:00
-- url     : https://prove2.me/submissions/2554d18f-32cf-4b4a-9ec4-ff18cb31a2e1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_lam_last_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_lastIdx
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_le_last
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_le_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_nu_zero_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_sum_colH


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
theorem _root_.solution (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu) :
    (((TCols lam).filter fun c => colH lam c = colH nu c + 1).card : ℤ) =
      ∑ a, lam a - ∑ a, nu a - lam (Fin.last m) := by
  have h1 : ∀ c, ((if colH lam c = colH nu c + 1 then 1 else 0 : ℕ) : ℤ) = (colH lam c : ℤ) - colH nu c := by
    intro c
    have := qr_colH_eq hi c
    omega
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, h1]
  rw [Finset.sum_sub_distrib, TCols, qr_lastIdx,
    qr_sum_colH lam _ _ (fun a => ⟨hl (Fin.le_last a), qr_le_zero hl a⟩),
    qr_sum_colH nu _ _ (fun a => ⟨(qr_lam_last_le hi).trans (qr_le_last hn a),
      (qr_le_zero hn a).trans (qr_nu_zero_le hi)⟩)]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
