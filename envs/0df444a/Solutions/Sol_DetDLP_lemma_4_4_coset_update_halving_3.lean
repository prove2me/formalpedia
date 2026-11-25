-- Prove2me | solution 3 for DetDLP.lemma_4_4_coset_update_halving
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:27:48.707608+00:00
-- url     : https://prove2.me/submissions/73c3a5ab-bc27-42eb-b243-4f52e6f58470

import Theorems.Thm_DetDLP_coset_update_algebraic
import Theorems.Thm_DetDLP_coset_intersection_hnf_machine

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem solution :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ (Mlab N : ℕ) [NeZero Mlab], 2 ≤ Mlab → 1 ≤ N →
        ∀ (x0 : Fin N → ZMod Mlab) (B : Matrix (Fin N) (Fin N) ℤ)
          (a : Fin N → ZMod Mlab) (c0 : ZMod Mlab),
          IsModularLatticeBasis Mlab B →
          let A := affineCoset Mlab x0 B
          let A' := {x ∈ A | ∑ i : Fin N, a i * x i = c0}
          A'.Nonempty →
          let gstar : ℕ :=
            Finset.univ.fold Nat.gcd Mlab
              (fun j : Fin N => Int.natAbs (∑ i : Fin N, ((a i).val : ℤ) * B i j))
          ∃ (x0' : Fin N → ZMod Mlab) (B' : Matrix (Fin N) (Fin N) ℤ),
            IsModularLatticeBasis Mlab B' ∧
            affineCoset Mlab x0' B' = A' ∧
            Nat.card A' * Mlab = Nat.card A * gstar ∧
            RunsWithin M out
              (encodeCosetUpdateInput Mlab (fun i => (x0 i).val) B (fun i => (a i).val) c0.val)
              (encodeCosetRep (fun i => (x0' i).val) B')
              (polyBound K (N + bitLen Mlab))
              (polyBound K (N + bitLen Mlab)) ∧
            ((∑ i : Fin N, a i * x0 i ≠ c0) → gstar < Mlab ∧ 2 * Nat.card A' ≤ Nat.card A) := by
  obtain ⟨M, out, K, run⟩ := DetDLP.coset_intersection_hnf_machine
  refine ⟨M, out, K, ?_⟩
  intro m N hNe hm hN x0 B a c hB A A' hnon d
  obtain ⟨x1, B1, hb1, hset, hrun⟩ := run m N hm hN x0 B a c hB hnon
  obtain ⟨_,_,_,_,hcard,hhalf⟩ := coset_update_algebraic m N hm hN x0 B a c hB hnon
  exact ⟨x1,B1,hb1,hset,hcard,hrun,hhalf⟩
