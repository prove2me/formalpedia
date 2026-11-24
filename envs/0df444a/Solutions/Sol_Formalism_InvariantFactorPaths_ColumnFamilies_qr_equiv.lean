-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:59:34.032577+00:00
-- url     : https://prove2.me/submissions/03fa2e05-ad8f-4fa1-b911-5d30f01a3dc1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ClosureBranching
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_TMat_j
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_TMat_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_j_inj


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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {m : ℕ} [NeZero m] {M : GLMod (m + 1)} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
    (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (ph : Matrix M.ι (TIdx lam) ℤ)
    (hE : (M.A * ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) : Matrix _ _ _) =
      (ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) * TMat lam : Matrix _ _ _))
    {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ} (hb : IsBlock h g1 t)
    (i : M.ι) (I' : TIdx nu) :
    ∑ k, evGL h (M.A i k) * ((ph k (qr_j hi I') : ℤ) : R) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) *
        ∑ K' : TIdx nu, ((ph i (qr_j hi K') : ℤ) : R) * evGL g1 (TMat nu K' I') := by
  have h1 := congrArg (evGL h) (congrFun (congrFun hE i) (qr_j hi I'))
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, eq_intCast, map_intCast] at h1
  rw [h1, Finset.mul_sum]
  symm
  apply Finset.sum_of_injOn (qr_j hi) (qr_j_inj hi).injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  · intro K _ hK
    rw [qr_TMat_zero hb hn hi K I' (fun K' hK' => hK ⟨K', Finset.mem_coe.2 (Finset.mem_univ _), hK'⟩), mul_zero]
  · intro K' _
    rw [qr_TMat_j hb hl hn hi]
    ring
end Formalism.InvariantFactorPaths.ColumnFamilies
