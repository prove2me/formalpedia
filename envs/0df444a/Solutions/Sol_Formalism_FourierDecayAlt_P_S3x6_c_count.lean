-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.c_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:50.960804+00:00
-- url     : https://prove2.me/submissions/0c23c4d3-6cb9-4fa5-b25b-59f7a6f63689

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_exists_frob
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_pow_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_count_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_nu

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
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution [DecidableEq K] (hq : Fintype.card K = q ^ 2) (n : ℕ) : ∀ c : K, c ^ q = c →
    (q : ℤ) * (univ.filter (fun w : Fin n → K => ∑ i, w i ^ q * w i = c)).card =
      if c = 0 then (q : ℤ) ^ (2 * n) + (-1) ^ n * (q - 1) * q ^ n else q ^ n * (q ^ n - (-1) ^ n) := by
  obtain ⟨σ, hσ⟩ := c_exists_frob K q hq
  induction n with
  | zero =>
    intro c _
    by_cases h0 : c = 0
    · simp [h0]
    · simp [h0, Ne.symm h0]
  | succ n ih =>
    intro c hc
    have hfix : ∀ x : K, (c - x ^ q * x) ^ q = c - x ^ q * x := by
      intro x
      rw [← hσ, map_sub, map_mul, hσ, hσ, hσ, hc, c_pow_pow K q hq, mul_comm]
    rw [c_count_succ, Nat.cast_sum, Finset.mul_sum, Finset.sum_congr rfl (fun x _ => ih _ (hfix x)),
      Finset.sum_ite, sum_const, sum_const, c_nu K q hq c hc]
    have h3 : ((univ.filter (fun x : K => ¬ (c - x ^ q * x = 0))).card : ℤ) =
        (q : ℤ) ^ 2 - (if c = 0 then 1 else q + 1 : ℕ) := by
      have h4 := Finset.card_filter_add_card_filter_not (s := (univ : Finset K)) (fun x : K => c - x ^ q * x = 0)
      rw [c_nu K q hq c hc, card_univ, hq] at h4
      have h5 : (((if c = 0 then 1 else q + 1 : ℕ) + (univ.filter (fun x : K => ¬ (c - x ^ q * x = 0))).card : ℕ) : ℤ)
          = ((q ^ 2 : ℕ) : ℤ) := by rw [h4]
      push_cast at h5 ⊢
      linarith
    rw [nsmul_eq_mul, nsmul_eq_mul, h3]
    by_cases h0 : c = 0
    · simp only [h0, if_true]
      push_cast
      ring
    · simp only [h0, if_false]
      push_cast
      ring
end Formalism.FourierDecayAlt.P.S3x6
