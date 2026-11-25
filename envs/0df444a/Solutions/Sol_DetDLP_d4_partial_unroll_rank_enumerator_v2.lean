-- Prove2me | solution 1 for DetDLP.d4_partial_unroll_rank_enumerator_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T07:21:20.134735+00:00
-- url     : https://prove2.me/submissions/f488c00e-1b25-453d-8d2d-f00ede927619
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DetDLP_d4_core_cut_and_unroll_tree_math
import Theorems.Thm_DetDLP_d4_rank_enumerator_machine
import Theorems.Thm_DetDLP_d4_stopped_source_evaluator_machine
import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem solution (one : AppendixD4.OneStep) (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) :
    ∃ (A : PrimitiveMachine) (oa : Fin A.tapeCount) (K L₀ : ℕ) (P : (x : Input C c) → L₀ ≤ Nat.clog 2 x.S → entry x E o → Plan x),
      (∀ x hl he, ∀ i < (P x hl he).f.natDegree, (P x hl he).f.coeff i = 0 ∨ (P x hl he).f.coeff i = 1) ∧
      (∀ x hl he, Enumerates A oa K (P x hl he)) ∧
      (AppendixD4.Closed → ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k : ℕ), ∀ x hl he, Sources B ob k (P x hl he)) := by
  obtain ⟨L₀, P, hcoeff⟩ := DetDLP.d4_core_cut_and_unroll_tree_math one C c hC hc E o
  obtain ⟨A, oa, K, henumerates⟩ := DetDLP.d4_rank_enumerator_machine one C c hC hc E o L₀ P hcoeff
  exact ⟨A, oa, K, L₀, P, hcoeff, henumerates,
    DetDLP.d4_stopped_source_evaluator_machine C c hC hc E o L₀ P⟩
