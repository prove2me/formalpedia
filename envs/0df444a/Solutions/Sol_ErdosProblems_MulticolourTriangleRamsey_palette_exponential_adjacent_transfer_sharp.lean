-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.palette_exponential_adjacent_transfer_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/2466d3d8-94f0-467e-9126-ec1445e62782

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution
    (H a k₀ k : ℕ)
    (hH : 3 ≤ H)
    (hlog : Real.log (H : ℝ) ≤ (a : ℝ))
    (hk₀ : k₀ ≤ k)
    (hratio : a * k ≤ (a + 34) * k₀) :
    ((H : ℝ) / Real.exp 38) ^ k ≤
      ((H : ℝ) / Real.exp 4) ^ k₀ := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have htarget : 0 < ((H : ℝ) / Real.exp 38) ^ k := by positivity
  have hsource : 0 < ((H : ℝ) / Real.exp 4) ^ k₀ := by positivity
  have hratioReal :
      (a : ℝ) * (k : ℝ) ≤
        ((a : ℝ) + 34) * (k₀ : ℝ) := by
    exact_mod_cast hratio
  have hdelta : 0 ≤ (k : ℝ) - (k₀ : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hk₀)
  have hweighted := mul_le_mul_of_nonneg_left hlog hdelta
  apply (Real.log_le_log_iff htarget hsource).mp
  rw [Real.log_pow, Real.log_pow,
    Real.log_div hHpos.ne' (Real.exp_ne_zero 38),
    Real.log_div hHpos.ne' (Real.exp_ne_zero 4),
    Real.log_exp, Real.log_exp]
  nlinarith
end ErdosProblems.MulticolourTriangleRamsey
