-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.clause
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:35:59.767499+00:00
-- url     : https://prove2.me/submissions/4c6918ac-506d-432f-accc-429b27bada29

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_span_prime
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_two_case
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_ram_case
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_odd_case
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
private theorem Kd_exists_isPrime_liesOver (p : ℕ) [hp : Fact p.Prime] :
    ∃ P : Ideal (𝓞 (Kd b)), P.IsPrime ∧ P.LiesOver (span {(p : ℤ)}) := by
  haveI hmax : (span {(p : ℤ)}).IsMaximal := by
    first
    | exact Int.ideal_span_isMaximal_of_prime p
    | exact (span_prime p).isMaximal (by simp [hp.out.ne_zero])
    | exact Ideal.IsPrime.isMaximal (span_prime p) (by simp [hp.out.ne_zero])
  first
  | (obtain ⟨P, hP⟩ := Ideal.nonempty_primesOver (S := 𝓞 (Kd b)) (span {(p : ℤ)}); exact ⟨P, hP.1, hP.2⟩)
  | (obtain ⟨P, hP, hPl⟩ := Ideal.exists_ideal_liesOver_maximal_of_isIntegral (span {(p : ℤ)}) (𝓞 (Kd b)); exact ⟨P, hP.isPrime, hPl⟩)
  | (obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 (Kd b)) (span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 (Kd b))).injective_int]; exact bot_le); exact ⟨Q, hQ.isPrime, ⟨hQc.symm⟩⟩)
end Formalism.FrobeniusOrbits.SplitK
namespace Formalism.FrobeniusOrbits
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
namespace Formalism.FrobeniusOrbits.SplitK
theorem _root_.solution (hd : d.Prime) (hd7 : d % 8 = 7) (hb : b ^ 2 = -(d : L)) (p : ℕ) (hp : p.Prime) :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 ↔
      (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(d : ℤ)) p = 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP1, hP2⟩ := Kd_exists_isPrime_liesOver (b := b) p
  haveI := hP1
  haveI := hP2
  by_cases h2 : p = 2
  · have h3 := two_case hd.pos hd7 hb p h2 P
    exact ⟨fun _ => Or.inl h2, fun _ => h3⟩
  · by_cases hpd : p = d
    · have h3 := ram_case hd hb p hpd P
      have hJ : jacobiSym (-(d : ℤ)) p = 0 := by
        subst hpd
        first
        | (rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd (by simp), jacobiSym.zero_left hp.one_lt])
        | (rw [jacobiSym.eq_zero_iff_not_coprime]; simp [Int.gcd_neg, Int.gcd_self]; exact hp.one_lt.ne')
      rw [h3, hJ]
      simp [h2]
    · have h3 := odd_case hd hb p h2 hpd P
      constructor
      · intro h
        exact Or.inr ⟨h2, h3.mp h⟩
      · rintro (h | ⟨-, h⟩)
        · exact absurd h h2
        · exact h3.mpr h
end Formalism.FrobeniusOrbits.SplitK
