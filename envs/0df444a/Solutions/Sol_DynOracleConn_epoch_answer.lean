-- Prove2me | solution 1 for DynOracleConn.epoch_answer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:36:28.080702+00:00
-- url     : https://prove2.me/submissions/701b9f2c-b8d4-4ded-b538-92a03074c4c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DynOracleConn_Gadget
import Theorems.Thm_DynOracleConn_gadget_isAcyclic
import Theorems.Thm_DynOracleConn_claim_3_1

open DynOracleConn

namespace AuxEpochAnswer

lemma walk_cons_of_ne {V : Type} {G : SimpleGraph V} {u v : V} (hne : u ≠ v)
    (w : G.Walk u v) : ∃ (x : V) (h : G.Adj u x) (rest : G.Walk x v), w = .cons h rest := by
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons h rest => exact ⟨_, h, rest, rfl⟩

lemma adj_t_withT_iff {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (i : Fin d) (u : Fin n) :
    (withT e X i).Adj (e GV.t) u ↔ u = e (GV.v false i) := by
  have ht_iso := (DynOracleConn.gadget_isAcyclic e X).2.2.1
  have htv_ne : e GV.t ≠ e (GV.v false i) := fun h => nomatch (e.injective h)
  constructor
  · intro hadj
    simp only [withT, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff,
      Sym2.eq_iff] at hadj
    rcases hadj with hg | ⟨hpair, _⟩
    · exact False.elim (ht_iso u hg)
    · rcases hpair with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact False.elim (htv_ne h1)
  · rintro rfl
    simp [withT, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, htv_ne]

lemma transfer_avoiding_t {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (i : Fin d) :
    ∀ {a b : Fin n} (p : (withT e X i).Walk a b),
      e GV.t ∉ p.support → (gadget e X).Reachable a b
  | a, _, .nil, _ => SimpleGraph.Reachable.refl a
  | a, c, .cons (v := b) hadj rest, hnot => by
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hnot
      have ha_ne : a ≠ e GV.t := fun h => hnot.1 h.symm
      have hb_ne : b ≠ e GV.t := fun h => hnot.2 (h ▸ SimpleGraph.Walk.start_mem_support rest)
      have hadj_g : (gadget e X).Adj a b := by
        simp only [withT, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff,
          Sym2.eq_iff] at hadj
        rcases hadj with hg | ⟨⟨h1, _⟩ | ⟨_, h2⟩, _⟩
        · exact hg
        · exact False.elim (ha_ne h1)
        · exact False.elim (hb_ne h2)
      exact hadj_g.reachable.trans (transfer_avoiding_t e X i rest hnot.2)

end AuxEpochAnswer

theorem solution {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (i : Fin d) :
    ((withT e X i).Reachable (e GV.s) (e GV.t) ↔ yval X i = false) ∧
    ¬ (gadget e X).Reachable (e GV.s) (e GV.t) := by
  have ht_iso := (DynOracleConn.gadget_isAcyclic e X).2.2.1
  have hst_ne : e GV.s ≠ e GV.t := fun h => nomatch (e.injective h)
  refine ⟨?_, ?_⟩
  · rw [← DynOracleConn.claim_3_1 e X i]
    constructor
    · intro hreach
      obtain ⟨w⟩ := hreach.symm
      let p := w.toPath
      have hp : p.val.IsPath := p.property
      obtain ⟨u, hadj, rest, hp_eq⟩ := AuxEpochAnswer.walk_cons_of_ne hst_ne.symm p.val
      rw [hp_eq, SimpleGraph.Walk.cons_isPath_iff] at hp
      have hu : u = e (GV.v false i) := (AuxEpochAnswer.adj_t_withT_iff e X i u).mp hadj
      subst hu
      exact (AuxEpochAnswer.transfer_avoiding_t e X i rest hp.2).symm
    · intro hreach
      have hsub : gadget e X ≤ withT e X i := le_sup_left
      have hreach_w : (withT e X i).Reachable (e GV.s) (e (GV.v false i)) :=
        SimpleGraph.Reachable.mono hsub hreach
      have hadj_vt : (withT e X i).Adj (e (GV.v false i)) (e GV.t) :=
        ((AuxEpochAnswer.adj_t_withT_iff e X i (e (GV.v false i))).mpr rfl).symm
      exact hreach_w.trans hadj_vt.reachable
  · rintro ⟨w⟩
    obtain ⟨u, hadj, _, _⟩ := AuxEpochAnswer.walk_cons_of_ne hst_ne.symm w.reverse
    exact ht_iso u hadj
