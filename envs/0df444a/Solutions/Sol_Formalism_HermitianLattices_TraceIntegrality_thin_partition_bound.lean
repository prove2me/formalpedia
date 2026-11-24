-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.thin_partition_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:00.731938+00:00
-- url     : https://prove2.me/submissions/d5f274b9-271c-4214-860c-9520308497b9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HookRowProductEqFactorial
import Theorems.Thm_Formalism_HermitianLattices_TraceIntegrality_hook_length_formula
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_hook_product_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
private lemma one_le_hook_product {N : ℕ} (nu : Fin N → ℕ) : 1 ≤ hookProd nu := by
  unfold hookProd
  refine Nat.succ_le_of_lt (prod_pos fun i _ => prod_pos fun j hj => ?_)
  have := mem_range.1 hj
  unfold hookLen
  omega
private lemma log_factorial_le_mul_log (n : ℕ) (M : ℝ) (hM : 1 ≤ M) (h : (n : ℝ) ≤ M) :
    Real.log (n.factorial : ℝ) ≤ M * Real.log M := by
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := by
          refine Real.log_le_log (by exact_mod_cast n.factorial_pos) ?_
          exact_mod_cast Nat.factorial_le_pow n
      _ = n * Real.log n := by rw [Real.log_pow]
      _ ≤ n * Real.log M := by
          exact mul_le_mul_of_nonneg_left (Real.log_le_log hn' h) hn'.le
      _ ≤ M * Real.log M := mul_le_mul_of_nonneg_right h hlM
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : ThinPlaceHookBound := by
  intro C₀ hC
  refine ⟨(3 + C₀) * (Real.log (3 + C₀) + 1) + (2 + C₀) * C₀, ?_⟩
  intro R nu b' L logOm hanti hrow hb hL hlb hR hOm
  have hl3 : 0 ≤ Real.log (3 + C₀) := Real.log_nonneg (by linarith)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  set M : ℝ := (3 + C₀) * b' with hMdef
  have hM1 : 1 ≤ M := by nlinarith
  have hlogM : Real.log M ≤ (Real.log (3 + C₀) + 1) * L := by
    rw [hMdef, Real.log_mul (by linarith) (by linarith)]
    nlinarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hform : (hookProd nu : ℝ) = hookF nu := hook_length_formula (R + 1) nu hanti
  have hF1 : 1 ≤ hookF nu := by
    rw [← hform]; exact_mod_cast one_le_hook_product nu
  have hlow : 0 ≤ Real.log (hookF nu) := Real.log_nonneg hF1
  have hup : Real.log (hookF nu) ≤ ((R : ℝ) + 1) * (M * Real.log M) := by
    have h1 := (Formalism.LogVandermondeBounds.flipTwoThree.hook_product_bounds R nu hanti).1
    calc Real.log (hookF nu)
        ≤ Real.log (∏ i : Fin (R + 1), ((nu i + R - i : ℕ).factorial : ℝ)) :=
          Real.log_le_log (by linarith) h1
      _ = ∑ i : Fin (R + 1), Real.log ((nu i + R - i : ℕ).factorial : ℝ) := by
          rw [Real.log_prod]
          intro i _
          exact_mod_cast (Nat.factorial_pos _).ne'
      _ ≤ ∑ _i : Fin (R + 1), M * Real.log M := by
          refine sum_le_sum fun i _ => log_factorial_le_mul_log _ M hM1 ?_
          have h2 : ((nu i + R - i : ℕ) : ℝ) ≤ (nu i : ℝ) + R := by
            exact_mod_cast Nat.sub_le _ _
          have h3 := hrow i
          rw [hMdef]; nlinarith
      _ = _ := by simp
  have hS0 : 0 ≤ ∑ i, (nu i : ℝ) := sum_nonneg fun i _ => Nat.cast_nonneg _
  have hS : ∑ i, (nu i : ℝ) ≤ ((R : ℝ) + 1) * ((2 + C₀) * b') := by
    calc ∑ i, (nu i : ℝ) ≤ ∑ _i : Fin (R + 1), (2 + C₀) * b' := sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  unfold placeTerm
  have hSO : |(∑ i, (nu i : ℝ)) * logOm| ≤ ((R : ℝ) + 1) * ((2 + C₀) * b') * (C₀ * L) := by
    rw [abs_mul, abs_of_nonneg hS0]
    exact mul_le_mul hS hOm (abs_nonneg _) (by positivity)
  have hML : M * Real.log M ≤ M * ((Real.log (3 + C₀) + 1) * L) :=
    mul_le_mul_of_nonneg_left hlogM (by linarith)
  have hup2 : ((R : ℝ) + 1) * (M * Real.log M) ≤ ((R : ℝ) + 1) * (M * ((Real.log (3 + C₀) + 1) * L)) :=
    mul_le_mul_of_nonneg_left hML (by linarith)
  calc |Real.log (hookF nu) - (∑ i, (nu i : ℝ)) * logOm|
      ≤ |Real.log (hookF nu)| + |(∑ i, (nu i : ℝ)) * logOm| := abs_sub _ _
    _ ≤ ((R : ℝ) + 1) * (M * ((Real.log (3 + C₀) + 1) * L))
          + ((R : ℝ) + 1) * ((2 + C₀) * b') * (C₀ * L) := by
        rw [abs_of_nonneg hlow]; linarith
    _ = _ := by rw [hMdef]; ring
end Formalism.HermitianLattices.TraceIntegrality
