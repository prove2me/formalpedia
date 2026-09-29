-- Prove2me | solution 1 for Erdos77.gnnw_uniform_ramsey_entropy_exponential_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T14:21:36.279868+00:00
-- url     : https://prove2.me/submissions/f298523f-cc26-43fc-a210-a3b27aaffbfb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_gnnw_uniform_ramsey_bound
import Theorems.Thm_Erdos77_uniform_binomial_entropy_upper_bound
import Definitions.Def_Erdos77_asymmetric_ramsey
import Mathlib
open Filter Topology

theorem solution :
  Exists fun w : Nat -> Real =>
    w =o[atTop] (fun k : Nat => (k : Real)) /\
    forall k ell : Nat, 0 < k -> 0 < ell -> ell <= k ->
      (Erdos77.asymmetricRamsey k ell : Real) <=
        Real.exp (((-(1 / 4 : Real) * ((ell : Real) / k) +
            (3 / 100 : Real) * ((ell : Real) / k) ^ 2 +
            (2 / 25 : Real) * ((ell : Real) / k) ^ 3) *
            Real.exp (-((ell : Real) / k)) +
            ((1 + ((ell : Real) / k)) * Real.log (1 + ((ell : Real) / k)) -
              ((ell : Real) / k) * Real.log ((ell : Real) / k))) * (k : Real) + w k) := by
  rcases Erdos77.gnnw_uniform_ramsey_bound with ⟨err, herr, hramsey⟩
  have hchoose := Erdos77.uniform_binomial_entropy_upper_bound
  refine ⟨err, herr, ?_⟩
  intro k ell hk hkell hle
  let x : Real := (ell : Real) / k
  let g : Real :=
    (-(1 / 4 : Real) * x + (3 / 100 : Real) * x ^ 2 +
      (2 / 25 : Real) * x ^ 3) * Real.exp (-x)
  let h : Real := (1 + x) * Real.log (1 + x) - x * Real.log x
  have hr := hramsey k ell hk hkell hle
  have hc := hchoose k ell hk hkell hle
  change (Erdos77.asymmetricRamsey k ell : Real) <=
      Real.exp (g * (k : Real) + err k) * (Nat.choose (k + ell) ell : Real) at hr
  change (Nat.choose (k + ell) ell : Real) <=
      Real.exp (h * (k : Real)) at hc
  change (Erdos77.asymmetricRamsey k ell : Real) <=
      Real.exp ((g + h) * (k : Real) + err k)
  calc
    (Erdos77.asymmetricRamsey k ell : Real) <=
        Real.exp (g * (k : Real) + err k) * (Nat.choose (k + ell) ell : Real) := hr
    _ <= Real.exp (g * (k : Real) + err k) *
          Real.exp (h * (k : Real)) :=
      mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
    _ = Real.exp ((g + h) * (k : Real) + err k) := by
      rw [← Real.exp_add]
      congr 1
      ring
