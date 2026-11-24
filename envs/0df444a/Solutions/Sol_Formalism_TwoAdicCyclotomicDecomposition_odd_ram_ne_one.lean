-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_ram_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:09.731879+00:00
-- url     : https://prove2.me/submissions/ed86d03d-5df5-474b-8e4a-1cc5f9b03f39

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_lift

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
theorem _root_.solution {L : Type} [Field L] [NumberField L] (r : ℕ) (hr : r.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})] (x : L)
    (hx : x ^ 2 = ((-(r : ℤ) : ℤ) : L)) :
    P.ramificationIdx ℤ ≠ 1 := by
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(r : ℤ)}) P (by simpa using hr.ne_zero)]
  have hmemq : ((r : ℤ) : 𝓞 L) ∈ P := (odd_intCast_mem_iff r P _).mpr dvd_rfl
  have hmap : map (algebraMap ℤ (𝓞 L)) (span {(r : ℤ)}) = span {((r : ℤ) : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, eq_intCast]
  rw [Ideal.ramificationIdx'_ne_one_iff
      (by rw [hmap, Ideal.span_le, Set.singleton_subset_iff]; exact hmemq),
    hmap, Ideal.span_le, Set.singleton_subset_iff]
  obtain ⟨A, -, hA2⟩ := odd_lift x _ hx
  have hA2P : A ^ 2 ∈ P := by
    rw [hA2, Int.cast_neg]
    exact P.neg_mem_iff.mpr hmemq
  have hAP : A ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem 2 hA2P
  have : ((r : ℤ) : 𝓞 L) = -(A * A) := by
    rw [← pow_two, hA2, Int.cast_neg, neg_neg]
  show ((r : ℤ) : 𝓞 L) ∈ P ^ 2
  rw [this, pow_two]
  exact (P * P).neg_mem_iff.mpr (Ideal.mul_mem_mul hAP hAP)
end Formalism.TwoAdicCyclotomicDecomposition
