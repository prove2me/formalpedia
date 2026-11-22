-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.fund
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:31.867217+00:00
-- url     : https://prove2.me/submissions/9549955d-465d-4de5-a41e-8de3c0d66191

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
    (P : Ideal (𝓞 (Kd b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard * (P.ramificationIdx ℤ * P.inertiaDeg ℤ) = 2 := by
  haveI : NumberField (Kd b) := by
    first
    | exact inferInstance
    | exact NumberField.mk
    | exact ⟨⟩
  haveI : IsGalois ℚ (Kd b) := Kd_isGalois_of_sq_eq_neg hd0 hb
  haveI : Finite (Kd b ≃ₐ[ℚ] Kd b) := Nat.finite_of_card_ne_zero (by rw [card_gal hd0 hb]; norm_num)
  haveI := span_prime p
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)})
    (𝓞 (Kd b)) (Kd b ≃ₐ[ℚ] Kd b)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P (Kd b ≃ₐ[ℚ] Kd b),
    Ideal.inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P (Kd b ≃ₐ[ℚ] Kd b), card_gal hd0 hb] at h
  exact h
end Formalism.FrobeniusOrbits.SplitK
