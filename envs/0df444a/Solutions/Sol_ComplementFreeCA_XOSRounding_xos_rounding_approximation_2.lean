-- Prove2me | solution 2 for ComplementFreeCA.XOSRounding.xos_rounding_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:04:21.394871+00:00
-- url     : https://prove2.me/submissions/22f5c0da-a284-493f-ba21-20c56dbfdea3

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSRounding_Model
import Definitions.Def_ComplementFreeCA_XOSRounding_Rounding
import Definitions.Def_ComplementFreeCA_XOSRounding_Algorithm
import Theorems.Thm_ComplementFreeCA_XOSRounding_expected_alg_ge_lp_value
import Theorems.Thm_ComplementFreeCA_XOSRounding_lp_optimum_ge_welfare

-- carved verbatim out of submission f0a8b89c-188e-44a1-b9f5-74e6d97ccf1d, lines 360-379

section
open Finset
open MeasureTheory Set ComplementFreeCA.XOSRounding

theorem solution {n m : ℕ} (hn : 0 < n)
    (W : Fin n → Finset (Fin m → ℝ)) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsXOSWith (v i) (W i))
    (cl : Fin n → Finset (Fin m) → Fin m → ℝ) (hcl : ∀ i, IsXOSOracle (v i) (W i) (cl i))
    (win : (Fin n → Finset (Fin m)) → Fin m → Fin n) (hwin : IsHighestClauseRule cl win)
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPOptimal v x)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    (1 - (1 - 1 / (n : ℝ)) ^ n) * welfare v O ≤
      roundingExpectation x (algWelfare v win) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hbase : 0 ≤ 1-1/(n:ℝ) := by
    rw [sub_nonneg, div_le_one hnR]
    exact_mod_cast (show 1 ≤ n by omega)
  have hupper : 1-1/(n:ℝ) ≤ 1 := by
    have h : (0:ℝ) ≤ 1/n := by positivity
    linarith
  have halpha : 0 ≤ 1-(1-1/(n:ℝ))^n := sub_nonneg.mpr (pow_le_one₀ hbase hupper)
  exact (mul_le_mul_of_nonneg_left (ComplementFreeCA.XOSRounding.lp_optimum_ge_welfare v x hx O hO) halpha).trans
    (ComplementFreeCA.XOSRounding.expected_alg_ge_lp_value hn W v hv cl hcl win hwin x hx.1)

end
