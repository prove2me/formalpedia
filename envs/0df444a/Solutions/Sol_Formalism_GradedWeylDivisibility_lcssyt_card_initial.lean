-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcssyt_card_initial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:49:27.173368+00:00
-- url     : https://prove2.me/submissions/ceae61ef-8566-456e-8e9b-23598dcc625a

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ t t' : Fin n, t' ≤ t → P t → P t') (t : Fin n) :
    t.val < (univ.filter P).card ↔ P t := by
  constructor
  · intro h
    by_contra hPt
    have hsub : univ.filter P ⊆ Iio t := by
      intro t' ht'
      simp only [mem_filter, mem_univ, true_and] at ht'
      simp only [mem_Iio]
      by_contra hle
      exact hPt (hP t' t (not_lt.mp hle) ht')
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro hPt
    have hsub : Iic t ⊆ univ.filter P := by
      intro t' ht'
      simp only [mem_Iic] at ht'
      simp only [mem_filter, mem_univ, true_and]
      exact hP t t' ht' hPt
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
end Formalism.GradedWeylDivisibility
