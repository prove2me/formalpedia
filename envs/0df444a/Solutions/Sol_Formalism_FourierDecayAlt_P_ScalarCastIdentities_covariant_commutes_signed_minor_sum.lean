-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.covariant_commutes_signed_minor_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:51.602993+00:00
-- url     : https://prove2.me/submissions/c96f852a-815d-431a-89f1-42a75bfe96e8

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_cast_mul_eq_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_skip_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_skip_one_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_eps_skip
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_skip_one_ne
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
theorem _root_.solution (hE : GlRel E) (η : Fin t → A) (hη : IsCov E η) (hηη : ∀ a b, η a * η b = η b * η a) (q c p : Fin t)
    (w : ℂ) : ∑ a, η a * nS E a q c p (w - 1) = ∑ a, nS E a q c p w * η a := by
  by_cases hcp : c = p
  · have h0 : ∀ a w', nS E a q c p w' = 0 := fun a w' => by rw [nS, if_pos (Or.inr hcp)]
    simp only [h0, mul_zero, zero_mul]
  rcases t with _ | _ | t
  · exact q.elim0
  · have h0 : ∀ a w', nS E a q c p w' = 0 := fun a w' => by rw [nS, if_pos (Or.inl (Fin.ext (by omega)))]
    simp only [h0, mul_zero, zero_mul]
  · have h := quantum_minor_move.2 A (t + 2) t E η hE hη hηη (skip1 q) (skip2 (min c p) (max c p)) w
    have hs : ∀ k : Fin (t + 1), (skip1 q ∘ k.succAbove : Fin t → Fin (t + 1 + 1)) =
        skip2 (min (skip1 q k) q) (max (skip1 q k) q) := fun k => skip_comp t q k
    simp only [hs, cast_mul_eq_smul] at h
    push_cast at h
    have key : ∀ (k : Fin (t + 1)) (w' : ℂ), nS E (q.succAbove k) q c p w' =
        ((((eps c p : ℤ) : ℂ) * (-1 : ℂ) ^ ((q : ℕ) + (c : ℕ) + (p : ℕ))) * (-1 : ℂ) ^ (k : ℕ)) •
          qminor E (skip2 (min (skip1 q k) q) (max (skip1 q k) q)) (skip2 (min c p) (max c p)) w' := by
      intro k w'
      rw [← skip_succ_identity, nS, if_neg (by have := skip_one_ne _ q k; tauto), ← eps_skip (t + 1) q k]
      congr 1
      ring
    have hq : ∀ w', nS E q q c p w' = 0 := fun w' => by rw [nS, if_pos (Or.inl rfl)]
    rw [Fin.sum_univ_succAbove _ q, Fin.sum_univ_succAbove _ q, hq, hq, mul_zero, zero_mul, zero_add, zero_add]
    have l1 : ∑ k : Fin (t + 1), η (q.succAbove k) * nS E (q.succAbove k) q c p (w - 1) =
        (((eps c p : ℤ) : ℂ) * (-1 : ℂ) ^ ((q : ℕ) + (c : ℕ) + (p : ℕ))) • ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ)) •
          (η (skip1 q k) * qminor E (skip2 (min (skip1 q k) q) (max (skip1 q k) q)) (skip2 (min c p) (max c p))
            (w - 1)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [key, mul_smul_comm, smul_smul, skip_succ_identity]
    have l2 : ∑ k : Fin (t + 1), nS E (q.succAbove k) q c p w * η (q.succAbove k) =
        (((eps c p : ℤ) : ℂ) * (-1 : ℂ) ^ ((q : ℕ) + (c : ℕ) + (p : ℕ))) • ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ)) •
          (qminor E (skip2 (min (skip1 q k) q) (max (skip1 q k) q)) (skip2 (min c p) (max c p)) w *
            η (skip1 q k)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [key, smul_mul_assoc, smul_smul, skip_succ_identity]
    rw [l1, l2, h]
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
