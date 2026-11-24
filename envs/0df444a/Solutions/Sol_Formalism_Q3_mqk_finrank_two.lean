-- Prove2me | solution 1 for Formalism.Q3.mqk_finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:40.283962+00:00
-- url     : https://prove2.me/submissions/5463a7b8-3b21-42e7-b0a8-a2634536f4b3

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
namespace Formalism.Q3
theorem _root_.solution (K : IntermediateField F E) (β b : E) (hb : b ∈ K) (hβ : β ^ 2 = b)
    (hns : ∀ z ∈ K, z ^ 2 ≠ b) :
    Module.finrank K (IntermediateField.adjoin K {β}) = 2 := by
  set b' : K := ⟨b, hb⟩ with hb'
  have hmon : (X ^ 2 - C b' : K[X]).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval β (X ^ 2 - C b' : K[X]) = 0 := by simp [b', hβ]
  have hint : IsIntegral K β := ⟨X ^ 2 - C b', hmon, by simpa [aeval_def] using hev⟩
  have hirr : Irreducible (X ^ 2 - C b' : K[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun z hz =>
      hns z z.2 (by simpa [b'] using congrArg Subtype.val hz)
  have hmin : minpoly K β = X ^ 2 - C b' := (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  rw [IntermediateField.adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]
end Formalism.Q3
