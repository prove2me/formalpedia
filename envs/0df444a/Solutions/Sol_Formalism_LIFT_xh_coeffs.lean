-- Prove2me | solution 1 for Formalism.LIFT.xh_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:55:25.076991+00:00
-- url     : https://prove2.me/submissions/3714f9db-49d0-4659-8661-6278293f8948

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Theorems.Thm_Formalism_LIFT_xh_comp
import Theorems.Thm_Formalism_LIFT_sum_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Finset
variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)
namespace Formalism.LIFT
theorem _root_.solution (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (n : ℕ) :
    ∀ m : ℕ → ℤ, X ^ H * ∑ k ∈ range (ℓ ^ n), (m k : A) * ε ^ k ∈ aa →
      ∀ k < ℓ ^ n, X ^ H * (m k : A) ∈ aa := by
  induction n with
  | zero =>
    intro m h k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simpa using h
  | succ n ih =>
    intro m h k hk
    let e : Fin ℓ → A := fun i => ∑ j ∈ range (ℓ ^ n), (m (i + ℓ * j) : A) * ε ^ j
    have hdec : ∑ k ∈ range (ℓ ^ (n + 1)), (m k : A) * ε ^ k =
        ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i) := by
      rw [pow_succ', ← sum_split (fun k => (m k : A) * ε ^ k) ℓ (ℓ ^ n)]
      refine sum_congr rfl fun i _ => ?_
      simp only [e, map_sum, map_mul, map_intCast, map_pow, hε, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [pow_add, ← pow_mul]
      ring
    rw [hdec] at h
    have hb := xh_comp φA ε aa hℓ hε hU X Q H hX hQ e h ⟨k % ℓ, Nat.mod_lt _ hℓ⟩
    have hk' : k / ℓ < ℓ ^ n := by
      rw [Nat.div_lt_iff_lt_mul hℓ]
      rw [pow_succ] at hk
      exact hk
    have := ih (fun j => m (k % ℓ + ℓ * j)) hb (k / ℓ) hk'
    simpa [Nat.mod_add_div] using this
end Formalism.LIFT
