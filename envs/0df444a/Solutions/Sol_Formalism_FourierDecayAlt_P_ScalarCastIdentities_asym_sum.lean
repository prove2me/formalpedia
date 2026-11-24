-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.asym_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:52:11.175418+00:00
-- url     : https://prove2.me/submissions/2f3d7a8e-90c0-4a1f-bcf9-402f456d4cc3

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant

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
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution {B : Type*} [AddCommGroup B] {t : ℕ} (T : Fin t → Fin t → Fin t → Fin t → B) :
    ∑ i, ∑ i', (if i < i' then T i i' i i' - T i' i i i' else 0) =
      ∑ a, ∑ b, if a = b then 0 else eps a b • T a b (min a b) (max a b) := by
  have h : ∀ a b : Fin t, (if a = b then 0 else eps a b • T a b (min a b) (max a b)) =
      (if a < b then T a b a b else 0) - (if b < a then T a b b a else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · have h' : a.val < b.val := h
      rw [if_neg h.ne, if_pos h, if_neg (not_lt.2 h.le), min_eq_left h.le, max_eq_right h.le, eps, if_pos h', one_smul,
        sub_zero]
    · subst h
      simp
    · have h' : ¬ a.val < b.val := not_lt.2 (le_of_lt h)
      rw [if_neg h.ne', if_neg (not_lt.2 h.le), if_pos h, min_eq_right h.le, max_eq_left h.le, eps, if_neg h', neg_smul,
        one_smul, zero_sub]
  simp_rw [h]
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if b < a then T a b b a else 0), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
