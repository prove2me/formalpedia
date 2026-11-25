-- Prove2me | solution 1 for DetDLP.factor_splitting_driver_machine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:03:24.629185+00:00
-- url     : https://prove2.me/submissions/4d8ee2d5-616e-465e-adbb-81afe0ef8b8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_Machine
import Theorems.Thm_DetDLP_divisor_bisection_and_btn_scale
import Theorems.Thm_DetDLP_splitting_tree_size_and_prime_power_from_factors
import Theorems.Thm_DetDLP_oracle_search_and_scan_tm_compilation

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution
    (f : ℕ → ℕ) (Md : PrimitiveMachine) (od : Fin Md.tapeCount) (Kd : ℕ)
    (hd : ∀ N : ℕ, 2 ≤ N →
      let n := bitLen (N+1)
      RunsWithin Md od (countWord N) (countWord (f N))
        ((2 : ℝ)^((Kd : ℝ)*n/Real.sqrt (logSafe n))) (polyBound Kd n)) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N+1)
        let split : ℕ → ℕ → List ℕ :=
          Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
            let d := f x
            if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x/d) else [x])
        RunsWithin M out (countWord N) (encodeNatListBin ((split n N).mergeSort))
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n) :=
  (DetDLP.oracle_search_and_scan_tm_compilation
    DetDLP.divisor_bisection_and_btn_scale
    DetDLP.splitting_tree_size_and_prime_power_from_factors).2.1 f Md od Kd hd
