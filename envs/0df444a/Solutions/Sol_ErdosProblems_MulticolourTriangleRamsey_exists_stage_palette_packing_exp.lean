-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_stage_palette_packing_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/a20bf742-98b0-4e1b-879b-64eb3983ac15

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_choose_le_exp_mul_div_pow
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_stage_palette_packing_binomial

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (j a s : ℕ)
    (hj : 0 < j) (ha : 2 ≤ a) (hs : 0 < s) :
    ∃ family : Finset (Finset (Fin (j * (a * s)))),
      family ⊆
        (Finset.univ : Finset (Fin (j * (a * s)))).powersetCard (a * s) ∧
      IsPaletteSeparated s family ∧
      (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
  have hhalf : 2 * s ≤ a * s := Nat.mul_le_mul_right s ha
  obtain ⟨family, hfamily, hseparated, hpacking⟩ :=
    exists_stage_palette_packing_binomial j (a * s) s hs hj hhalf
  refine ⟨family, hfamily, hseparated, ?_⟩
  have hreal :
      (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) *
          ((s * (a * s).choose s * (j * (a * s)).choose s : ℕ) : ℝ) := by
    exact_mod_cast hpacking
  have hfirst := choose_le_exp_mul_div_pow (a * s) s hs
  have hsecond := choose_le_exp_mul_div_pow (j * (a * s)) s hs
  have hbase :
      (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) *
        (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) =
          Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ) := by
    push_cast
    field_simp
  have hpowers :
      (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
        (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s =
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
    rw [← mul_pow, hbase]
  calc
    (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) *
          ((s * (a * s).choose s * (j * (a * s)).choose s : ℕ) : ℝ) :=
      hreal
    _ = (family.card : ℝ) * (s : ℝ) *
          ((a * s).choose s : ℝ) *
          ((j * (a * s)).choose s : ℝ) := by
      push_cast
      ring
    _ ≤ (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
          (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s := by
      gcongr
    _ = (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
      calc
        (family.card : ℝ) * (s : ℝ) *
            (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
            (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s =
          (family.card : ℝ) * (s : ℝ) *
            ((Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
              (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s) := by
                ring
        _ = (family.card : ℝ) * (s : ℝ) *
            (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
              rw [hpowers]
end ErdosProblems.MulticolourTriangleRamsey
