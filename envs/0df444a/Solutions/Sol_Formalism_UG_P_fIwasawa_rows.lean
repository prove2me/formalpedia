-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_rows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:20.033481+00:00
-- url     : https://prove2.me/submissions/279955f0-833d-4e74-8cf1-06257ba6c3b1

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
import Theorems.Thm_Formalism_UG_P_fIwasawa_gram_un
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaRed
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
private theorem sigma_diag_mul_rev_diag_and_rev_entries_zero (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (m : ℕ) : ∀ s : Fin n, s.val = m → s.val < r →
      σ (M s s) * M (Fin.rev s) (Fin.rev s) = 1 ∧
        ∀ b : Fin n, b < Fin.rev s → M (Fin.rev s) b = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s hsm hs
    have key : ∀ b : Fin n, b ≤ Fin.rev s →
        σ (M s s) * M (Fin.rev s) b = if b = Fin.rev s then 1 else 0 := by
      intro b hb
      rw [← fIwasawa_gram_un σ M hM s b, Finset.sum_eq_single (Fin.rev s)]
      · rw [Fin.rev_rev]
      · intro j _ hj
        have hne : Fin.rev j ≠ s := fun h => hj (by rw [← h, Fin.rev_rev])
        rcases lt_or_gt_of_ne hne with h | h
        · have hjs : (Fin.rev j).val < m := by
            rw [← hsm]
            exact h
          have hjr : (Fin.rev j).val < r := by omega
          have hjb : b < Fin.rev (Fin.rev j) := by
            have := b.isLt
            have := j.isLt
            have := s.isLt
            rw [Fin.rev_rev]
            rw [Fin.le_def, Fin.val_rev] at hb
            rw [Fin.lt_def, Fin.val_rev] at h
            rw [Fin.lt_def]
            omega
          have h0 := (ih _ hjs (Fin.rev j) rfl hjr).2 b hjb
          rw [Fin.rev_rev] at h0
          rw [h0, mul_zero]
        · rw [hT (Fin.rev j) s hs h, map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h1 := key (Fin.rev s) le_rfl
    rw [if_pos rfl] at h1
    refine ⟨h1, fun b hb => ?_⟩
    have h2 := key b hb.le
    rw [if_neg (ne_of_lt hb)] at h2
    exact (mul_eq_zero.mp h2).resolve_left (left_ne_zero_of_mul_eq_one h1)
end FIwasawaRed
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (s : Fin n) (hs : s.val < r) :
    σ (M s s) * M (Fin.rev s) (Fin.rev s) = 1 ∧
      ∀ b : Fin n, b < Fin.rev s → M (Fin.rev s) b = 0 := by
  exact sigma_diag_mul_rev_diag_and_rev_entries_zero σ M hM r hT s.val s rfl hs
end Formalism.UG.P
