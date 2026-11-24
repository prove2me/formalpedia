-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.ncard_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:41.968951+00:00
-- url     : https://prove2.me/submissions/1fea2b73-880e-4d86-8e33-27789ba009cc

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_finrank_K
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_quad_K
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_card_gal
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_span_prime
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
private theorem Kd_isGalois_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : IsGalois ℚ (Kd b) := by
  first
  | exact IsGalois.of_card_aut_eq_finrank (by rw [card_gal hd hb, finrank_K hd hb])
  | exact IsGalois.of_card_aut_eq_finrank ℚ (Kd b) (by rw [card_gal hd hb, finrank_K hd hb])
  | (haveI := quad_K hd hb; exact inferInstance)
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
theorem _root_.solution (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (Kd b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (h : ∀ σ : Kd b ≃ₐ[ℚ] Kd b, σ • P = P) :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 1 := by
  haveI : NumberField (Kd b) := by
    first
    | exact inferInstance
    | exact NumberField.mk
    | exact ⟨⟩
  haveI : IsGalois ℚ (Kd b) := Kd_isGalois_of_sq_eq_neg hd0 hb
  haveI : Finite (Kd b ≃ₐ[ℚ] Kd b) := Nat.finite_of_card_ne_zero (by rw [card_gal hd0 hb]; norm_num)
  haveI := span_prime p
  have hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 (Kd b)) := by
    first
    | exact ⟨inferInstance, inferInstance⟩
    | exact ⟨‹_›, ‹_›⟩
    | (simp only [Ideal.primesOver, Set.mem_setOf_eq]; exact ⟨inferInstance, inferInstance⟩)
  rw [Set.ncard_eq_one]
  refine ⟨P, Set.eq_singleton_iff_unique_mem.mpr ⟨hP, fun Q hQ => ?_⟩⟩
  have hex : ∃ σ : Kd b ≃ₐ[ℚ] Kd b, σ • P = Q := by
    first
    | (obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Kd b ≃ₐ[ℚ] Kd b) (⟨P, hP⟩ : primesOver (span {(p : ℤ)}) (𝓞 (Kd b))) ⟨Q, hQ⟩; exact ⟨σ, congrArg Subtype.val hσ⟩)
    | (haveI := hQ.1; haveI := hQ.2; exact Ideal.exists_smul_eq_of_isGaloisGroup (span {(p : ℤ)}) P Q (Kd b ≃ₐ[ℚ] Kd b))
  obtain ⟨σ, h1⟩ := hex
  rw [← h1, h σ]
end Formalism.FrobeniusOrbits.SplitK
