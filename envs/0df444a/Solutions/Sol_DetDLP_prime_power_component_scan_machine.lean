-- Prove2me | solution 1 for DetDLP.prime_power_component_scan_machine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:03:27.318882+00:00
-- url     : https://prove2.me/submissions/70fe98df-4606-439e-861a-bb85866290eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_divisor_bisection_and_btn_scale
import Theorems.Thm_DetDLP_splitting_tree_size_and_prime_power_from_factors
import Theorems.Thm_DetDLP_oracle_search_and_scan_tm_compilation

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution
    (Mf : PrimitiveMachine) (ofac : Fin Mf.tapeCount) (Kf : ℕ)
    (hfac : ∀ N : ℕ, 2 ≤ N →
      let n := bitLen (N+1)
      RunsWithin Mf ofac (countWord N) (encodeNatListBin N.primeFactorsList)
        ((2 : ℝ)^((Kf : ℝ)*n/Real.sqrt (logSafe n))) (polyBound Kf n))
    (Me : PrimitiveMachine) (oe : Fin Me.tapeCount) (Ke : ℕ) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        ∀ F : Fin m → List (ZMod p)ˣ,
          RunsWithin Me oe (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound Ke b) (mainSpaceBound Ke b) →
          let n := p-1
          let U := (List.ofFn F).flatten
          let h : (ZMod p)ˣ := ∏ r ∈ n.primeFactors,
            ((U.find? (fun u => decide (u^(n/r) ≠ 1))).getD 1) ^ (n / r^(n.factorization r))
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C b) (mainSpaceBound C b) :=
  (DetDLP.oracle_search_and_scan_tm_compilation
    DetDLP.divisor_bisection_and_btn_scale
    DetDLP.splitting_tree_size_and_prime_power_from_factors).2.2 Mf ofac Kf hfac Me oe Ke
