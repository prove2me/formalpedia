-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_TMat_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:50:25.748376+00:00
-- url     : https://prove2.me/submissions/e0c7f2a6-b6d1-4618-891e-115c56ed699a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_minorC
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_j_surj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_minor_zero


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
theorem _root_.solution (hb : IsBlock h g1 t) (hn : Dominant nu) (hi : Interl lam nu) (K : TIdx lam) (I' : TIdx nu)
    (hK : ∀ K', qr_j hi K' ≠ K) : evGL h (TMat lam K (qr_j hi I')) = 0 := by
  have h1 : ∃ c : ↥(TCols lam), ¬ (Fin.last m ∈ (K c).1 ↔ colH lam c = colH nu c + 1) := by
    by_contra hcon
    obtain ⟨K', hK'⟩ := qr_j_surj hn hi K (fun c => by
      by_contra h2; exact hcon ⟨c, h2⟩)
    exact hK K' hK'
  obtain ⟨c, hc⟩ := h1
  simp only [TMat, map_mul, map_prod, qc_evGL_minorC]
  rw [Finset.prod_eq_zero (Finset.mem_univ c), mul_zero]
  exact qr_minor_zero hb _ _ _ _ _ hc
end Formalism.InvariantFactorPaths.ColumnFamilies
