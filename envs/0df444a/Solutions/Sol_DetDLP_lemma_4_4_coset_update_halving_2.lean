-- Prove2me | solution 2 for DetDLP.lemma_4_4_coset_update_halving
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:23:58.633966+00:00
-- url     : https://prove2.me/submissions/8c9fd2ff-16e7-4f68-8fac-81072cf12f49
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset
import Theorems.Thm_DetDLP_coset_update_card_and_halving
import Theorems.Thm_DetDLP_coset_update_hnf_tm

set_option autoImplicit false

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
  obtain ⟨M, out, K, hTM⟩ := DetDLP.coset_update_hnf_tm
  refine ⟨M, out, K, ?_⟩
  intro Mlab N _ hM hN x0 B a c0 hB
  dsimp only
  intro hA'ne
  obtain ⟨x0', B', hB', hcoset, hrun⟩ := hTM Mlab N hM hN x0 B a c0 hB hA'ne
  obtain ⟨hcard, hhalve⟩ :=
    DetDLP.coset_update_card_and_halving Mlab N hM hN x0 B a c0 hA'ne
  exact ⟨x0', B', hB', hcoset, hcard, hrun, hhalve⟩
