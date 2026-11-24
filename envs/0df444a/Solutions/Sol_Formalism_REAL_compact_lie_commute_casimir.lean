-- Prove2me | solution 1 for Formalism.REAL.compact_lie_commute_casimir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:34:31.938453+00:00
-- url     : https://prove2.me/submissions/fe3f8d98-7030-4e51-bf05-f48890a41461

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] {n : ℕ} {ε : Fin n → Bool} {F : Fin n → Fin n → A}
    (h : KRel ε F) {a b : Fin n} (hab : ε a = ε b) : F a b * CasK ε F = CasK ε F * F a b := by
  rw [← sub_eq_zero]
  have key : ∀ c d, F a b * (if ε c = ε d then F c d * F d c else 0) -
      (if ε c = ε d then F c d * F d c else 0) * F a b =
      (if b = c then (if ε c = ε d then F a d * F d c else 0) else 0)
      - (if d = a then (if ε c = ε d then F c b * F d c else 0) else 0)
      + (if b = d then (if ε c = ε d then F c d * F a c else 0) else 0)
      - (if c = a then (if ε c = ε d then F c d * F d b else 0) else 0) := by
    intro c d
    by_cases hcd : ε c = ε d
    · simp only [if_pos hcd]
      have e1 := h a b c d hab hcd
      have e2 := h a b d c hab hcd.symm
      calc F a b * (F c d * F d c) - F c d * F d c * F a b
          = (F a b * F c d - F c d * F a b) * F d c + F c d * (F a b * F d c - F d c * F a b) := by
            noncomm_ring
        _ = _ := by
            rw [e1, e2]
            simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
            abel
    · simp [hcd]
  unfold CasK
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun c d => if b = c then (if ε c = ε d then F a d * F d c else 0) else 0),
    Finset.sum_comm (f := fun c d => if c = a then (if ε c = ε d then F c d * F d b else 0) else 0)]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, hab]
  abel
end Formalism.REAL
