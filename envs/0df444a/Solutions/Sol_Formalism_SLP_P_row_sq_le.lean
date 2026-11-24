-- Prove2me | solution 1 for Formalism.SLP.P.row_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:26.065917+00:00
-- url     : https://prove2.me/submissions/00660f77-7ab4-4b4e-be96-c6d645f89770

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset ComplexConjugate
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
namespace Formalism.SLP.P
theorem _root_.solution (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ) (hB : ∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖)
    {m : ℕ} (x : V₁) (hx : ‖x‖ = 1) (f : Fin m → V₂) (hf : Orthonormal ℂ f) :
    ∑ l, ‖B x (f l)‖ ^ 2 ≤ c ^ 2 := by
  set a : Fin m → ℂ := fun l => B x (f l) with ha
  set y : V₂ := ∑ l, a l • f l with hy
  set S : ℝ := ∑ l, ‖a l‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun l _ => by positivity
  have h1 : B x y = (S : ℂ) := by
    rw [hy, map_sum, hS]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, Complex.conj_mul']
  have h2 : ‖y‖ ^ 2 = S := by
    rw [@norm_sq_eq_re_inner ℂ, hy, hf.inner_sum, hS, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.conj_mul']
    norm_cast
  have h3 : S ≤ c * ‖y‖ := by
    have := hB x y
    rw [h1, hx, mul_one, Complex.norm_real, Real.norm_of_nonneg hS0] at this
    exact this
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · have h4 : S * S ≤ c ^ 2 * S := by
      have h5 : 0 ≤ c * ‖y‖ := le_trans hS0 h3
      calc S * S ≤ (c * ‖y‖) * (c * ‖y‖) := mul_le_mul h3 h3 hS0 h5
        _ = c ^ 2 * S := by rw [← h2]; ring
    exact le_of_mul_le_mul_right h4 h0
end Formalism.SLP.P
