-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:04.040931+00:00
-- url     : https://prove2.me/submissions/bea1d958-0aaa-4bac-be6a-1ec97ec857fd

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_densP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (q : ℕ) (hq : 0 < q) (s : ℕ → ℕ)
    (hs : ∀ n, (q : ℤ) * s n = q ^ n * (q ^ n - (-1) ^ n)) (b : ℕ) :
    ((∏ j ∈ Finset.range b, s (j + 1) : ℕ) : ℝ) = (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b := by
  rw [d_densP]
  have hq' : (q : ℝ) ≠ 0 := by positivity
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.cast_mul, ih]
    have h1 : (q : ℝ) * s (b + 1) = q ^ (b + 1) * (q ^ (b + 1) - (-1) ^ (b + 1)) := by
      exact_mod_cast hs (b + 1)
    have h2 : (s (b + 1) : ℝ) = q ^ b * (q ^ (b + 1) - (-1) ^ (b + 1)) := by
      apply mul_left_cancel₀ hq'
      rw [h1]; ring
    rw [h2]
    have h3 : (b + 1) ^ 2 = b ^ 2 + b + (b + 1) := by ring
    rw [h3, pow_add, pow_add]
    generalize (∏ i ∈ Finset.range b, (1 - ((-1 : ℤ) : ℝ) ^ (i + 1) * ((q : ℝ) ^ (i + 1))⁻¹)) = Q
    have h4 : (q : ℝ) ^ (b + 1) * (1 - ((-1 : ℤ) : ℝ) ^ (b + 1) * ((q : ℝ) ^ (b + 1))⁻¹) =
        q ^ (b + 1) - (-1) ^ (b + 1) := by
      push_cast
      field_simp
    linear_combination (-(q : ℝ) ^ (b ^ 2) * Q * q ^ b) * h4
end Formalism.FourierDecayAlt.P.S3x6
