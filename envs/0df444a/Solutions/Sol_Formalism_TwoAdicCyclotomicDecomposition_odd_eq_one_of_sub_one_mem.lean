-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_eq_one_of_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:08.163299+00:00
-- url     : https://prove2.me/submissions/8e545826-789a-458a-a08b-1c0fb64c1766

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) {η : S}
    {m : ℕ} (hη : η ^ m = 1) (hm : (m : S) ∉ P) (h : η - 1 ∈ P) : η = 1 := by
  by_contra hne
  have hsum : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := geom_sum_mul η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hmem : ∑ i ∈ Finset.range m, (η ^ i - 1) ∈ P := Ideal.sum_mem _ fun i _ => by
    rw [← geom_sum_mul η i]
    exact P.mul_mem_left _ h
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_one,
    zero_sub] at hmem
  exact hm (P.neg_mem_iff.mp hmem)
end Formalism.TwoAdicCyclotomicDecomposition
