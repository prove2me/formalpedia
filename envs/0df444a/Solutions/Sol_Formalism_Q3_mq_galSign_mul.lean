-- Prove2me | solution 1 for Formalism.Q3.mq_galSign_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:38.7316+00:00
-- url     : https://prove2.me/submissions/a2dc9c3b-8619-48b0-b47e-11c395df289f

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
import Theorems.Thm_Formalism_Q3_mq_alpha_ne_zero
import Theorems.Thm_Formalism_Q3_mq_sigma

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
variable {k : ℕ} {E : Type} [Field E] [NumberField E] {a : Fin k → ℤ} {α : Fin k → E}
namespace Formalism.Q3
theorem _root_.solution (h : IsMQ a α) (ha : ∀ i, a i ≠ 0) (σ τ : Gal(E/ℚ)) :
    galSign α (σ * τ) = galSign α σ * galSign α τ := by
  funext i
  have hne := mq_alpha_ne_zero h ha i
  have hστ := mq_sigma h (σ * τ) i
  rw [AlgEquiv.mul_apply, mq_sigma h τ i, map_mul, map_intCast, mq_sigma h σ i] at hστ
  have hcoef : (((galSign α (σ * τ) i : ℤˣ) : ℤ) : E) = (((galSign α σ i * galSign α τ i : ℤˣ) : ℤ) : E) := by
    have := hστ.symm
    rw [show ((((galSign α τ i : ℤˣ) : ℤ) : E) * ((((galSign α σ i : ℤˣ) : ℤ) : E) * α i)) =
      (((galSign α σ i * galSign α τ i : ℤˣ) : ℤ) : E) * α i by push_cast; ring] at this
    exact mul_right_cancel₀ hne this
  have := Int.cast_injective (α := E) hcoef
  exact Units.ext this
end Formalism.Q3
