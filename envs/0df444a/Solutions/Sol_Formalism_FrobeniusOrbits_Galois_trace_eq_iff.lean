-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.trace_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:06.331684+00:00
-- url     : https://prove2.me/submissions/4377b8d3-8c05-4ebb-bdca-8c9bfbd6c160

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_pow_val_eq_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_pow_val_mul_eq_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hζ : IsPrimitiveRoot ζ N) (u c : ZMod N) :
    ζ ^ u.val + ζ⁻¹ ^ u.val = ζ ^ c.val + ζ⁻¹ ^ c.val ↔ u = c ∨ u = -c := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)

  have key : ∀ x y : K, x ≠ 0 → y ≠ 0 → (x + x⁻¹ = y + y⁻¹ ↔ x = y ∨ x * y = 1) := by
    intro x y hx hy
    have hx' : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
    have hy' : y * y⁻¹ = 1 := mul_inv_cancel₀ hy
    have e : (x - y) * (x * y - 1) = x * y * ((x + x⁻¹) - (y + y⁻¹)) := by
      linear_combination (-y) * hx' + x * hy'
    constructor
    · intro hxy
      rw [hxy, sub_self, mul_zero] at e
      rcases mul_eq_zero.1 e with h1 | h1
      · exact Or.inl (sub_eq_zero.1 h1)
      · exact Or.inr (sub_eq_zero.1 h1)
    · rintro (h1 | h1)
      · rw [h1]
      · rw [eq_inv_of_mul_eq_one_right h1, inv_inv, add_comm]
  rw [inv_pow, inv_pow, key _ _ (pow_ne_zero _ h0) (pow_ne_zero _ h0), pow_val_eq_iff hζ,
    pow_val_mul_eq_one_iff hζ, eq_neg_iff_add_eq_zero]
end Formalism.FrobeniusOrbits.Galois
