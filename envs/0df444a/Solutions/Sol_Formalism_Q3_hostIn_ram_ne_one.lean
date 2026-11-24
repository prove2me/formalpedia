-- Prove2me | solution 1 for Formalism.Q3.hostIn_ram_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:33.375076+00:00
-- url     : https://prove2.me/submissions/41c77c85-041a-480b-b8a7-c13841dc419c

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia
import Theorems.Thm_Formalism_Q3_hostIn_intCast_mem_iff
import Theorems.Thm_Formalism_Q3_hostIn_A

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
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (i : Fin 3) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(q i : ℤ)})] :
    P.ramificationIdx ℤ ≠ 1 := by
  have hq0 : (q i : ℤ) ≠ 0 := by exact_mod_cast (hq.1 i).1.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(q i : ℤ)}) P (by simpa using (hq.1 i).1.ne_zero)]
  have hmemq : ((q i : ℤ) : 𝓞 E) ∈ P := (hostIn_intCast_mem_iff (q i) P _).mpr dvd_rfl
  have hmap : map (algebraMap ℤ (𝓞 E)) (span {(q i : ℤ)}) = span {((q i : ℤ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, eq_intCast]
  rw [Ideal.ramificationIdx'_ne_one_iff
      (by rw [hmap, Ideal.span_le, Set.singleton_subset_iff]; exact hmemq),
    hmap, Ideal.span_le, Set.singleton_subset_iff]
  obtain ⟨A, -, hA2⟩ := hostIn_A q α hα i
  have hA2P : A ^ 2 ∈ P := by
    rw [hA2, Int.cast_neg]
    exact P.neg_mem_iff.mpr hmemq
  have hAP : A ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem 2 hA2P
  have : ((q i : ℤ) : 𝓞 E) = -(A * A) := by
    rw [← pow_two, hA2, Int.cast_neg, neg_neg]
  show ((q i : ℤ) : 𝓞 E) ∈ P ^ 2
  rw [this, pow_two]
  exact (P * P).neg_mem_iff.mpr (Ideal.mul_mem_mul hAP hAP)
end Formalism.Q3
