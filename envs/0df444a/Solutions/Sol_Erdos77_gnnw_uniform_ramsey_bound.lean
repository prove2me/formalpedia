-- Prove2me | solution 1 for Erdos77.gnnw_uniform_ramsey_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:07:17.672326+00:00
-- url     : https://prove2.me/submissions/54de80f5-a01a-4721-9f8b-b9b36f53b6be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_gnnw_uniform_ramsey_entropy_exponential_bound
import Theorems.Thm_Erdos77_uniform_binomial_entropy_lower_bound
import Definitions.Def_Erdos77_asymmetric_ramsey
import Mathlib
open Filter Topology

theorem solution :
    Exists fun err : Nat -> Real =>
      err =o[atTop] (fun k : Nat => (k : Real)) /\
      forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
        (Erdos77.asymmetricRamsey k ell : Real) <=
          Real.exp (((-(1 / 4 : Real) * ((ell : Real) / k) +
            (3 / 100 : Real) * ((ell : Real) / k) ^ 2 +
            (2 / 25 : Real) * ((ell : Real) / k) ^ 3) *
            Real.exp (-((ell : Real) / k))) * (k : Real) + err k) *
            (Nat.choose (k + ell) ell : Real) := by
  rcases Erdos77.gnnw_uniform_ramsey_entropy_exponential_bound with
    ⟨w, hw, hbound⟩
  rcases Erdos77.uniform_binomial_entropy_lower_bound with
    ⟨xi, hxi, hchoose⟩
  refine ⟨fun k => w k + xi k, hw.add hxi, ?_⟩
  intro k ell hk hkell hle
  let x : Real := (ell : Real) / k
  let g : Real := (-(1 / 4 : Real) * x +
    (3 / 100 : Real) * x ^ 2 + (2 / 25 : Real) * x ^ 3) * Real.exp (-x)
  let h : Real := (1 + x) * Real.log (1 + x) - x * Real.log x
  have hram := hbound k ell hk hkell hle
  have hbin := hchoose k ell hk hkell hle
  change (Erdos77.asymmetricRamsey k ell : Real) <=
      Real.exp ((g + h) * (k : Real) + w k) at hram
  change Real.exp (h * (k : Real) - xi k) <=
      (Nat.choose (k + ell) ell : Real) at hbin
  change (Erdos77.asymmetricRamsey k ell : Real) <=
      Real.exp (g * (k : Real) + (w k + xi k)) *
        (Nat.choose (k + ell) ell : Real)
  calc
    (Erdos77.asymmetricRamsey k ell : Real) <=
        Real.exp ((g + h) * (k : Real) + w k) := hram
    _ = Real.exp (g * (k : Real) + (w k + xi k)) *
          Real.exp (h * (k : Real) - xi k) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ <= Real.exp (g * (k : Real) + (w k + xi k)) *
          (Nat.choose (k + ell) ell : Real) := by
      exact mul_le_mul_of_nonneg_left hbin (Real.exp_pos _).le
