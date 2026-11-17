-- Prove2me | solution 1 for DirKECC1549.Asm.bwalk_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T07:05:01.730688+00:00
-- url     : https://prove2.me/submissions/85b4a5ab-71dd-4cfb-920d-084b72e022ab

import Definitions.Def_DirKECC1549_Impl_FlowBfs

set_option autoImplicit false

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (H : Fin m → Fin n × Fin n) (z r : Fin n) (q : List (Fin n)) (h : ℕ)
    (par : Fin n → Fin m) (hS : FState H z q h par) (i : ℕ) (hi : i < q.length) (h0 : 0 < i)
    (t : List (Fin m)) (hW : BWalk H q par r i hi t) :
    ∃ j, ∃ hj : j < i, (H (par q[i])).1 = q[j]'(by omega) ∧
      BWalk H q par r j (by omega) (par q[i] :: t) := by
  obtain ⟨a1, j, hj, a2⟩ := hS.parent i hi h0
  refine ⟨j, hj, a2, ⟨⟨IsWalk.cons _ _ a2 (by rw [a1]; exact hW.1.1), ?_⟩, ?_⟩⟩
  · rw [List.nodup_cons]
    refine ⟨fun hm => ?_, hW.1.2⟩
    obtain ⟨j', hj', hlt, heq⟩ := hW.2 _ hm
    have e1 := (hS.parent j' hj' (by omega)).1
    rw [← heq, a1] at e1
    have := (List.Nodup.getElem_inj_iff hS.nd).1 e1
    omega
  · intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨i, hi, hj, rfl⟩
    · obtain ⟨j', hj', hlt, heq⟩ := hW.2 e he
      exact ⟨j', hj', by omega, heq⟩
