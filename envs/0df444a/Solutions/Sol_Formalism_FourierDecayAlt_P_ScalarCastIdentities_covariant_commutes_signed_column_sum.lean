-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.covariant_commutes_signed_column_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:34.133967+00:00
-- url     : https://prove2.me/submissions/51afa1d3-dcb6-4d97-8a83-8aab35505cc5

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_cast_mul_eq_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_skip_succ_identity
import Theorems.Thm_quantum_minor_move


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution (hE : GlRel E) (η : Fin t → A) (hη : IsCov E η) (hηη : ∀ a b, η a * η b = η b * η a) (j : Fin t)
    (w : ℂ) : ∑ i, η i * mS E i j (w - 1) = ∑ i, mS E i j w * η i := by
  rcases t with _ | t
  · exact j.elim0
  · have h := quantum_minor_move.2 A (t + 1) t E η hE hη hηη id (skip1 j) w
    have hs : ∀ i : Fin (t + 1), (id ∘ i.succAbove : Fin t → Fin (t + 1)) = skip1 i := fun i =>
      funext fun k => (skip_succ_identity t i k).symm
    simp only [hs, id, cast_mul_eq_smul] at h
    push_cast at h
    have l1 : ∑ i, η i * mS E i j (w - 1) = ((-1 : ℂ) ^ (j : ℕ)) •
        ∑ i : Fin (t + 1), ((-1 : ℂ) ^ (i : ℕ)) • (η i * qminor E (skip1 i) (skip1 j) (w - 1)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mS, mul_smul_comm, smul_smul, pow_add, mul_comm]
    have l2 : ∑ i, mS E i j w * η i = ((-1 : ℂ) ^ (j : ℕ)) •
        ∑ i : Fin (t + 1), ((-1 : ℂ) ^ (i : ℕ)) • (qminor E (skip1 i) (skip1 j) w * η i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mS, smul_mul_assoc, smul_smul, pow_add, mul_comm]
    rw [l1, l2, h]
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
