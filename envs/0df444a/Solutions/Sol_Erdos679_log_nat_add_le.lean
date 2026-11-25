-- Prove2me | solution 1 for Erdos679.log_nat_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:29.006893+00:00
-- url     : https://prove2.me/submissions/5f1390e1-d1de-47bc-a8d6-d14e2647e4e2

module
public import Definitions.Def_Erdos679_Analytic
public import Definitions.Def_Erdos679_Gap
public import Definitions.Def_Erdos679_CRT
public import Definitions.Def_Erdos679AdditiveRefutation_Solution

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (P K : ℕ) (hP : 0 < P) :
    log ((P + K : ℕ) : ℝ) ≤ log (P : ℝ) + K := by
  have hp : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hpone : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hsum : (0 : ℝ) < (P : ℝ) + K := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsum hp)
  rw [Real.log_div hsum.ne' hp.ne'] at hlog
  have hratio : ((P : ℝ) + K) / P ≤ (K : ℝ) + 1 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hpone)]
  push_cast
  linarith
end Erdos679
