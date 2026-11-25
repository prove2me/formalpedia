-- Prove2me | solution 1 for DetDLP.fp_primitive_root_scan_tm_compile
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T13:39:09.702263+00:00
-- url     : https://prove2.me/submissions/96121f5a-b153-42ef-b996-8e6f9d27bbac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_proposition_2_6_det_factorization
import Theorems.Thm_DetDLP_prime_power_component_scan_machine

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    (∃ (M_fac : PrimitiveMachine) (out_fac : Fin M_fac.tapeCount) (K_fac : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M_fac out_fac (countWord N) (encodeNatListBin N.primeFactorsList)
          (mainSpaceBound K_fac n) (mainSpaceBound K_fac n)) →
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount) (C_fb : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ i : Fin m, (F i).Nodup) ∧
          ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤ mainSpaceBound C_fb b ∧
          RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound C_fb b) (mainSpaceBound C_fb b) ∧
          (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1)) →
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1) ∧
          let U : List (ZMod p)ˣ := (List.ofFn F).flatten
          let a : ℕ → (ZMod p)ˣ := fun π =>
            (U.find? (fun u => decide (u ^ ((p - 1) / π) ≠ 1))).getD 1
          let h : (ZMod p)ˣ :=
            ∏ π ∈ (p - 1).primeFactors,
              (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C b) (mainSpaceBound C b) := by
  intro _ hfb
  obtain ⟨Mf, ofac, Kf, hfac⟩ := DetDLP.proposition_2_6_det_factorization
  obtain ⟨Me, oe, Ke, hMe⟩ := hfb
  obtain ⟨M, out, C, hTM⟩ :=
    DetDLP.prime_power_component_scan_machine Mf ofac Kf hfac Me oe Ke
  refine ⟨M, out, C, fun p _ => ?_⟩
  obtain ⟨F, _, _, hrun_enum, hwit⟩ := hMe p
  exact ⟨F, hwit, hTM p F hrun_enum⟩
