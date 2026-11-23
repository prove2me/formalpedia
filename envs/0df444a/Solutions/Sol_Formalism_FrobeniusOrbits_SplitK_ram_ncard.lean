-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.ram_ncard
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:14.60097+00:00
-- url     : https://prove2.me/submissions/523a314d-d0cb-42ca-b4f6-2027b89bbfa8

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_span_prime
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_ram_case
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
theorem _root_.solution (hd : d.Prime) (hb : b ^ 2 = -(d : L)) :
    (primesOver (span {(d : ℤ)}) (𝓞 (Kd b))).ncard = 1 := by
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨P, hP1, hP2⟩ := Kd_exists_isPrime_liesOver (b := b) d
  haveI := hP1
  haveI := hP2
  exact ram_case hd hb d rfl P
end Formalism.FrobeniusOrbits.SplitK
