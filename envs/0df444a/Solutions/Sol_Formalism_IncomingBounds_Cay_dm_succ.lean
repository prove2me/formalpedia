-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.dm_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:03.6748+00:00
-- url     : https://prove2.me/submissions/914f7941-7887-4929-82cb-0749d8f1f603

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_dm_add
import Theorems.Thm_Formalism_IncomingBounds_Cay_dm_monomial
import Theorems.Thm_Formalism_IncomingBounds_Cay_mfact_ne
import Theorems.Thm_Formalism_IncomingBounds_Cay_mfact_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {σ : Type} (x : σ) (m : σ →₀ ℕ) (Q : MvPolynomial σ K) :
    dm (Finsupp.single x 1 + m) Q = pderiv x (dm m Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [dm_monomial, dm_monomial]
    by_cases hma : m ≤ a
    · rw [if_pos hma, pderiv_monomial]
      by_cases hbx : (a - m) x = 0
      · have hn : ¬ (Finsupp.single x 1 + m ≤ a) := by
          intro h
          have h' := (Finsupp.le_def.mp h) x
          rw [Finsupp.tsub_apply] at hbx
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at h'
          omega
        rw [if_neg hn, hbx, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
      · have hle : Finsupp.single x 1 + m ≤ a := by
          rw [Finsupp.le_def]
          intro i
          have hmi := (Finsupp.le_def.mp hma) i
          rw [Finsupp.tsub_apply] at hbx
          by_cases hxi : x = i
          · subst hxi
            simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
            omega
          · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne (Ne.symm hxi)]
            omega
        have hsub : a - (Finsupp.single x 1 + m) = a - m - Finsupp.single x 1 := by
          rw [add_comm (Finsupp.single x 1) m, tsub_add_eq_tsub_tsub]
        rw [if_pos hle, hsub]
        congr 1
        have hfp := mfact_step (a - m) x (Nat.pos_of_ne_zero hbx)
        have h1 : (Formalism.IncomingBounds.mfact (a - m - Finsupp.single x 1) : K) ≠ 0 := mfact_ne _
        have h2 : (((a - m) x : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hbx
        rw [hfp, Nat.cast_mul]
        first
          | (field_simp; ring)
          | field_simp
    · have hn : ¬ (Finsupp.single x 1 + m ≤ a) := fun h => hma (le_trans le_add_self h)
      rw [if_neg hma, if_neg hn, map_zero]
  | add p q hp hq => rw [dm_add, dm_add, hp, hq, map_add]
end Formalism.IncomingBounds.Cay
