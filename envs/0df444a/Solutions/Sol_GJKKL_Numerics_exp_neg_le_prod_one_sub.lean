-- Prove2me | solution 1 for GJKKL.Numerics.exp_neg_le_prod_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:27.463228+00:00
-- url     : https://prove2.me/submissions/db99f5fd-6c27-4d1e-920f-5e948e98d322

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
public import Theorems.Thm_GJKKL_Numerics_sum_log_ge

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real
namespace GJKKL.Numerics
theorem _root_.solution (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : (m : ℝ) ≤ a) :
    exp (-(m : ℝ)) ≤ ∏ i ∈ range m, (1 - (i : ℝ) / a) := by
  have hpos : ∀ i ∈ range m, 0 < (a - i) / a := by
    intro i hi
    have : (i : ℝ) < m := by exact_mod_cast mem_range.mp hi
    exact div_pos (by linarith) ha
  have hprod : ∏ i ∈ range m, (1 - (i : ℝ) / a) = exp (∑ i ∈ range m, log ((a - i) / a)) := by
    rw [exp_sum]
    refine prod_congr rfl fun i hi => ?_
    rw [exp_log (hpos i hi)]
    field_simp
  rw [hprod, exp_le_exp]
  have hF := sum_log_ge a ha m hm
  have hlog : log ((a - m) / a) ≤ 0 :=
    log_nonpos (div_nonneg (by linarith) ha.le) (by rw [div_le_one ha]; linarith)
  have : 0 ≤ (a - m) * -log ((a - m) / a) := mul_nonneg (by linarith) (by linarith)
  nlinarith
end GJKKL.Numerics
