-- Prove2me | solution 2 for DetDLP.fp_primitive_root_tm_from_oracles
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:40.002251+00:00
-- url     : https://prove2.me/submissions/435d377e-1dd4-4138-ab97-7d9395aa52c4

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_primitive_root_scan_correctness
import Theorems.Thm_DetDLP_prime_power_component_scan_machine

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    (∃ (M_fac : PrimitiveMachine) (out_fac : Fin M_fac.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M_fac out_fac (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n)) →
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount) (C_fb : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        let gord := p - 1
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ i : Fin m, (F i).Nodup) ∧
          ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
            (C_fb : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) ∧
          RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound C_fb b) (mainSpaceBound C_fb b) ∧
          (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1)) →
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ a : ℕ → (ZMod p)ˣ,
          (∀ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π) ≠ 1) ∧
          let h := ∏ π ∈ (p - 1).primeFactors,
            (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C (bitLen p)) (mainSpaceBound C (bitLen p)) := by
  intro hfac hfb
  obtain ⟨M_fac, out_fac, K, hM_fac⟩ := hfac
  obtain ⟨M_enum, out_enum, C_fb, hM_enum⟩ := hfb
  obtain ⟨M, out, C, hTM⟩ :=
    DetDLP.prime_power_component_scan_machine M_fac out_fac K hM_fac M_enum out_enum C_fb
  refine ⟨M, out, C, fun p _ => ?_⟩
  obtain ⟨F, _, _, hrun_enum, hwit⟩ := hM_enum p
  have hrun := hTM p F hrun_enum
  let U : List (ZMod p)ˣ := (List.ofFn F).flatten
  let a : ℕ → (ZMod p)ˣ := fun π =>
    (U.find? (fun u => decide (u ^ ((p - 1) / π) ≠ 1))).getD 1
  have ha := (DetDLP.primitive_root_scan_correctness p (blockCount (bitLen p)) F hwit).1
  exact ⟨a, ha, hrun⟩
