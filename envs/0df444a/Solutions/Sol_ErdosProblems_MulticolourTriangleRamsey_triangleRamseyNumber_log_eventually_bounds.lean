-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_eventually_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/c4091256-069c-4492-9705-55c8b78fcd43

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_factorial_upper
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_quantitativeLowerBound_explicit_all

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution :
    ∀ᶠ k : ℕ in atTop,
      (1 / 6 : ℝ) * (k : ℝ) * Real.log (k : ℝ) ≤
          Real.log (triangleRamseyNumber k : ℝ) ∧
        Real.log (triangleRamseyNumber k : ℝ) ≤
          2 * (k : ℝ) * Real.log (k : ℝ) := by
  have hconstant : 0 < (1 / (6 * Real.exp 38) : ℝ) := by positivity
  have hlogsmall :
      ∀ᶠ k : ℕ in atTop,
        ‖Real.log (k : ℝ)‖ ≤
          (1 / (6 * Real.exp 38) : ℝ) *
            ‖(k : ℝ) ^ ((1 : ℝ) / 6)‖ := by
    simpa [Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))).bound hconstant
  filter_upwards [hlogsmall, eventually_ge_atTop 4] with k hsmall hk
  have hkpositive : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlogpositive : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hrootpositive : 0 < (k : ℝ) ^ ((1 : ℝ) / 6) :=
    Real.rpow_pos_of_pos hkpositive _
  have hsmall' :
      Real.log (k : ℝ) ≤
        (1 / (6 * Real.exp 38) : ℝ) * (k : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [Real.norm_eq_abs, abs_of_pos hlogpositive,
      Real.norm_eq_abs, abs_of_pos hrootpositive] at hsmall
    exact hsmall
  have hrootsquare :
      (k : ℝ) ^ ((1 : ℝ) / 6) * (k : ℝ) ^ ((1 : ℝ) / 6) =
        (k : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hkpositive]
    norm_num
  have hbase :
      (k : ℝ) ^ ((1 : ℝ) / 6) ≤
        ((1 : ℝ) / (6 * Real.exp 38)) *
          (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) := by
    apply (le_div_iff₀ hlogpositive).mpr
    calc
      (k : ℝ) ^ ((1 : ℝ) / 6) * Real.log (k : ℝ) ≤
          (k : ℝ) ^ ((1 : ℝ) / 6) *
            ((1 / (6 * Real.exp 38) : ℝ) *
              (k : ℝ) ^ ((1 : ℝ) / 6)) := by gcongr
      _ = (1 / (6 * Real.exp 38) : ℝ) *
            ((k : ℝ) ^ ((1 : ℝ) / 6) *
              (k : ℝ) ^ ((1 : ℝ) / 6)) := by ring
      _ = (1 / (6 * Real.exp 38) : ℝ) *
            (k : ℝ) ^ ((1 : ℝ) / 3) := by rw [hrootsquare]
  have hramsey :
      ((k : ℝ) ^ ((1 : ℝ) / 6)) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
    calc
      ((k : ℝ) ^ ((1 : ℝ) / 6)) ^ k ≤
          (((1 : ℝ) / (6 * Real.exp 38)) *
            (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k := by gcongr
      _ ≤ (triangleRamseyNumber k : ℝ) :=
        quantitativeLowerBound_explicit_all k (by omega)
  have hramseypositive : 0 < (triangleRamseyNumber k : ℝ) :=
    lt_of_lt_of_le (pow_pos hrootpositive k) hramsey
  have hkpow : k ≤ k ^ k :=
    le_self_pow (by omega : 1 ≤ k) (by omega : k ≠ 0)
  have hfour : 4 ≤ k ^ k := by omega
  have huppernat : triangleRamseyNumber k ≤ (k ^ k) ^ 2 := by
    calc
      triangleRamseyNumber k ≤ 4 * k.factorial :=
        triangleRamseyNumber_factorial_upper k
      _ ≤ 4 * k ^ k := Nat.mul_le_mul_left 4 (Nat.factorial_le_pow k)
      _ ≤ (k ^ k) * (k ^ k) := Nat.mul_le_mul_right (k ^ k) hfour
      _ = (k ^ k) ^ 2 := by ring
  have hupperreal :
      (triangleRamseyNumber k : ℝ) ≤ (((k : ℝ) ^ k) ^ 2) := by
    exact_mod_cast huppernat
  constructor
  · calc
      (1 / 6 : ℝ) * (k : ℝ) * Real.log (k : ℝ) =
          Real.log (((k : ℝ) ^ ((1 : ℝ) / 6)) ^ k) := by
            rw [Real.log_pow, Real.log_rpow hkpositive]
            ring
      _ ≤ Real.log (triangleRamseyNumber k : ℝ) :=
        Real.log_le_log (pow_pos hrootpositive k) hramsey
  · calc
      Real.log (triangleRamseyNumber k : ℝ) ≤
          Real.log (((k : ℝ) ^ k) ^ 2) :=
        Real.log_le_log hramseypositive hupperreal
      _ = 2 * (k : ℝ) * Real.log (k : ℝ) := by
        rw [Real.log_pow, Real.log_pow]
        ring
end ErdosProblems.MulticolourTriangleRamsey
