-- Prove2me | solution 1 for CombOpt.TutteBerge.exposed_add_two_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T06:21:07.323955+00:00
-- url     : https://prove2.me/submissions/40ce6266-a073-48f3-af0c-9be7854c8570

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Covers
import Definitions.Def_CombOpt_TutteBerge_Multigraph_exposedNodes
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching

open CombOpt.TutteBerge in
theorem solution {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E)
    (M : Set E) (hM : G.IsMatching M) :
    {v : V | G.Covers M v}.ncard = 2 * M.ncard ∧
      (G.exposedNodes M).ncard + 2 * M.ncard = Nat.card V := by
  classical
  cases nonempty_fintype V
  cases nonempty_fintype E
  have h2 : ∀ z : Sym2 V, ¬ z.IsDiag → (Finset.univ.filter (fun v => v ∈ z)).card = 2 := by
    intro z
    induction z using Sym2.ind with
    | h a b =>
      intro hd
      have hab : a ≠ b := by simpa using hd
      rw [show Finset.univ.filter (fun v => v ∈ s(a, b)) = {a, b} by ext; simp]
      exact Finset.card_pair hab
  have hcov : {v | G.Covers M v} =
      ↑(M.toFinset.biUnion (fun e => Finset.univ.filter (fun v => v ∈ G.ends e))) := by
    ext v; simp [Multigraph.Covers]
  have h1 : {v : V | G.Covers M v}.ncard = 2 * M.ncard := by
    rw [hcov, Set.ncard_coe_finset, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun e he => h2 _ (hM.1 e (Set.mem_toFinset.mp he))),
        Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card', mul_comm]
    · intro e he f hf hef
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro v hv hv'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
      exact hef (hM.2 e (Set.mem_toFinset.mp he) f (Set.mem_toFinset.mp hf) v hv hv')
  refine ⟨h1, ?_⟩
  rw [← h1]
  have := Set.ncard_add_ncard_compl {v : V | G.Covers M v}
  have e : G.exposedNodes M = {v | G.Covers M v}ᶜ := rfl
  rw [e]
  omega
