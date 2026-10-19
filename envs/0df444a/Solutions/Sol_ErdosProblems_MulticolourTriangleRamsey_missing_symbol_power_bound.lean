-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.missing_symbol_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/d8e7bde8-7e75-4fed-b56c-fb969123ae00

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    (H : ℝ) ^ 2 * ((H : ℝ) - 1) ^ (m + 1) <
      (H : ℝ) ^ (m + 1) := by
  have hHpos : 0 < (H : ℝ) := by
    exact_mod_cast (show 0 < H by omega)
  have hfrac_nonneg : 0 ≤ 1 - 1 / (H : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hHpos).mpr
    norm_num
    exact_mod_cast (show 1 ≤ H by omega)
  have hfrac_exp : 1 - 1 / (H : ℝ) ≤
      Real.exp (-(1 / (H : ℝ))) := by
    linarith [Real.add_one_le_exp (-(1 / (H : ℝ)))]
  have hfrac_strict :
      (1 - 1 / (H : ℝ)) ^ (m + 1) < ((H : ℝ) ^ 2)⁻¹ := by
    calc
      (1 - 1 / (H : ℝ)) ^ (m + 1) ≤
          Real.exp (-(1 / (H : ℝ))) ^ (m + 1) :=
        pow_le_pow_left₀ hfrac_nonneg hfrac_exp _
      _ = Real.exp (-((m + 1 : ℕ) : ℝ) / (H : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ < Real.exp (-2 * Real.log (H : ℝ)) := by
        apply Real.exp_strictMono
        apply (div_lt_iff₀ hHpos).mpr
        push_cast
        nlinarith
      _ = ((H : ℝ) ^ 2)⁻¹ := by
        rw [show -2 * Real.log (H : ℝ) =
          -(Real.log (H : ℝ) + Real.log (H : ℝ)) by ring]
        rw [Real.exp_neg, Real.exp_add, Real.exp_log hHpos, ← pow_two]
  have hidentity : 1 - 1 / (H : ℝ) = ((H : ℝ) - 1) / H := by
    field_simp
  rw [hidentity, div_pow] at hfrac_strict
  have hcross := (div_lt_div_iff₀
    (pow_pos hHpos (m + 1)) (pow_pos hHpos 2)).mp
      (show ((H : ℝ) - 1) ^ (m + 1) / (H : ℝ) ^ (m + 1) <
        1 / (H : ℝ) ^ 2 by simpa [one_div] using hfrac_strict)
  simpa [mul_comm] using hcross
end ErdosProblems.MulticolourTriangleRamsey
