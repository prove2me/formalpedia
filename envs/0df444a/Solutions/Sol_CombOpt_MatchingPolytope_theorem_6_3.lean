-- Prove2me | solution 1 for CombOpt.MatchingPolytope.theorem_6_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T11:59:32.625211+00:00
-- url     : https://prove2.me/submissions/bd3b5d9f-91cc-4579-b876-831da83d5a10

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsMatching
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsPerfectMatching
import Definitions.Def_CombOpt_MatchingPolytope_charVec
import Definitions.Def_CombOpt_MatchingPolytope_Graph_cut
import Definitions.Def_CombOpt_MatchingPolytope_Graph_system63
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_constraint_subset_polytope_aux

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CombOpt.MatchingPolytope.P816

open CombOpt.MatchingPolytope Classical

variable {V E : Type*} [Fintype V] [Fintype E]

theorem ends_eq (G : Graph V E) (hG : G.IsLoopless) (e : E) :
    ∃ a b : V, a ≠ b ∧ G.ends e = s(a, b) := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (G.ends e)
  refine ⟨a, b, ?_, hab.symm⟩
  intro h
  apply hG e
  rw [← hab]
  exact (Sym2.mk_isDiag_iff).2 h

theorem sum_charVec (M T : Finset E) :
    ∑ e ∈ T, charVec M e = ((T.filter (· ∈ M)).card : ℝ) := by
  simp only [charVec]
  rw [Finset.sum_boole]

theorem mem_cut_iff (G : Graph V E) {e : E} {a b : V} (hab : G.ends e = s(a, b))
    (A : Finset V) : e ∈ G.cut A ↔ (a ∈ A ∨ b ∈ A) ∧ (a ∉ A ∨ b ∉ A) := by
  simp [Graph.cut, hab, Sym2.mem_iff, or_and_right, exists_or]

theorem system63_convex (G : Graph V E) : Convex ℝ G.system63 := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨fun v => ?_, fun S h3 hodd => ?_, fun e => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx1 v, hy1 v]
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hx2 S h3 hodd) ha
    have h2 := mul_le_mul_of_nonneg_left (hy2 S h3 hodd) hb
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx3 e; have := hy3 e
    positivity

theorem filter_cut_single (G : Graph V E) (hG : G.IsLoopless) (M : Finset E) (v : V) :
    (G.cut {v}).filter (· ∈ M) = M.filter (fun e => v ∈ G.ends e) := by
  ext e
  obtain ⟨a, b, hab, he⟩ := ends_eq G hG e
  simp only [Finset.mem_filter, mem_cut_iff G he, Finset.mem_singleton, he, Sym2.mem_iff]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    refine ⟨h2, ?_⟩
    rcases h1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro ⟨h2, h1⟩
    refine ⟨⟨?_, ?_⟩, h2⟩
    · rcases h1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rcases h1 with h | h
      · exact Or.inr (fun h' => hab (h'.trans h).symm)
      · exact Or.inl (fun h' => hab (h'.trans h))

theorem pm_card (G : Graph V E) (M : Finset E) (hM : G.IsPerfectMatching M) (v : V) :
    (M.filter (fun e => v ∈ G.ends e)).card = 1 := by
  apply le_antisymm
  · convert hM.1 v
  · obtain ⟨e, heM, hv⟩ := hM.2 v
    exact Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨heM, hv⟩⟩

theorem charVec_mem (G : Graph V E) (hG : G.IsLoopless) (M : Finset E)
    (hM : G.IsPerfectMatching M) : charVec M ∈ G.system63 := by
  refine ⟨fun v => ?_, fun S h3 hodd => ?_, fun e => ?_⟩
  · rw [sum_charVec, filter_cut_single G hG, pm_card G M hM v]
    norm_num
  · rw [sum_charVec]
    by_contra hlt0
    have hlt := not_le.mp hlt0
    have hnc : ∀ e ∈ M, e ∉ G.cut S := by
      intro e he hc
      have hne : ((G.cut S).filter (· ∈ M)).Nonempty := ⟨e, Finset.mem_filter.2 ⟨hc, he⟩⟩
      have h1 : (1 : ℝ) ≤ ((G.cut S).filter (· ∈ M)).card := by
        exact_mod_cast Finset.card_pos.2 hne
      linarith
    have hdc : ∑ e ∈ M, (S.filter (fun v => v ∈ G.ends e)).card = S.card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm, Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [← Finset.card_filter]
      exact pm_card G M hM v
    have hev : Even (∑ e ∈ M, (S.filter (fun v => v ∈ G.ends e)).card) := by
      apply Finset.even_sum
      intro e he
      obtain ⟨a, b, hab, hend⟩ := ends_eq G hG e
      have hn := hnc e he
      rw [mem_cut_iff G hend] at hn
      by_cases ha : a ∈ S
      · have hb : b ∈ S := by tauto
        have hfe : S.filter (fun v => v ∈ G.ends e) = {a, b} := by
          ext v
          simp only [Finset.mem_filter, hend, Sym2.mem_iff, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro (rfl | rfl)
            · exact ⟨ha, Or.inl rfl⟩
            · exact ⟨hb, Or.inr rfl⟩
        rw [hfe, Finset.card_pair hab]
        exact even_two
      · have hb : b ∉ S := by tauto
        have hfe : S.filter (fun v => v ∈ G.ends e) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro v hv hve
          rw [hend, Sym2.mem_iff] at hve
          rcases hve with rfl | rfl
          · exact ha hv
          · exact hb hv
        rw [hfe, Finset.card_empty]
        exact ⟨0, rfl⟩
    rw [hdc] at hev
    exact (Nat.not_even_iff_odd.2 hodd) hev
  · simp only [charVec]
    split_ifs <;> norm_num

/-- The same graph in the vocabulary of `OAI.MatchingEntropy.LooplessGraph`. -/
noncomputable def toL (G : Graph V E) (hG : G.IsLoopless) :
    OAI.MatchingEntropy.LooplessGraph V E where
  left e := (G.ends e).out.1
  right e := (G.ends e).out.2
  loopless e h := hG e (by
    have hs : G.ends e = s((G.ends e).out.1, (G.ends e).out.2) := by
      conv_lhs => rw [← Quot.out_eq (G.ends e)]
    rw [hs]
    exact Sym2.mk_isDiag_iff.2 h)

theorem out_spec (G : Graph V E) (e : E) :
    G.ends e = s((G.ends e).out.1, (G.ends e).out.2) := by
  conv_lhs => rw [← Quot.out_eq (G.ends e)]

theorem mem_iff_incident (G : Graph V E) (hG : G.IsLoopless) (v : V) (e : E) :
    v ∈ G.ends e ↔ (toL G hG).Incident v e := by
  rw [out_spec G e, Sym2.mem_iff]
  simp only [OAI.MatchingEntropy.LooplessGraph.Incident, toL]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem cut_eq (G : Graph V E) (hG : G.IsLoopless) (S : Finset V) :
    G.cut S = (toL G hG).cut S := by
  ext e
  rw [OAI.MatchingEntropy.LooplessGraph.mem_cut, mem_cut_iff G (out_spec G e)]
  simp only [OAI.MatchingEntropy.LooplessGraph.Crosses, toL]
  tauto

theorem system63_subset (G : Graph V E) (hG : G.IsLoopless) :
    G.system63 ⊆ convexHull ℝ {x | ∃ M : Finset E, G.IsPerfectMatching M ∧ x = charVec M} := by
  intro x hx
  obtain ⟨hdeg, hodd, hnn⟩ := hx
  have hcut_univ : G.cut Finset.univ = ∅ := by
    ext e
    simp [Graph.cut]
  have heven : Even (Fintype.card V) := by
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    have hc : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    rcases Nat.lt_or_ge (Fintype.card V) 3 with h | h
    · have h1 : Fintype.card V = 1 := by obtain ⟨k, hk⟩ := hne; omega
      obtain ⟨v, hv⟩ := Fintype.card_eq_one_iff.1 h1
      have h2 := hdeg v
      have hs : ({v} : Finset V) = Finset.univ := by
        ext w
        simp [hv w]
      rw [hs, hcut_univ, Finset.sum_empty] at h2
      exact zero_ne_one h2
    · have h2 := hodd Finset.univ (by rw [hc]; exact h) (by rw [hc]; exact hne)
      rw [hcut_univ, Finset.sum_empty] at h2
      linarith
  have hxL : x ∈ (toL G hG).constraintPolytope := by
    refine ⟨hnn, fun v => ?_, fun S hS => ?_⟩
    · rw [← OAI.MatchingEntropy.LooplessGraph.cutMass_singleton,
        OAI.MatchingEntropy.LooplessGraph.cutMass, ← cut_eq G hG]
      exact hdeg v
    · rw [OAI.MatchingEntropy.LooplessGraph.cutMass, ← cut_eq G hG]
      rcases Nat.lt_or_ge S.card 3 with h | h
      · have h1 : S.card = 1 := by obtain ⟨k, hk⟩ := hS; omega
        obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 h1
        rw [hdeg v]
      · exact hodd S h hS
  have hmem := OAI.MatchingEntropy.LooplessGraph.constraint_subset_polytope_aux
    (Fintype.card V) (toL G hG) rfl heven hxL
  refine convexHull_mono ?_ hmem
  rintro _ ⟨M, rfl⟩
  refine ⟨M.1, ⟨fun v => ?_, fun v => ?_⟩, ?_⟩
  · obtain ⟨e, ⟨heM, hie⟩, huniq⟩ := M.2 v
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter, mem_iff_incident G hG] at ha hb
    exact (huniq a ha).trans (huniq b hb).symm
  · obtain ⟨e, ⟨heM, hie⟩, _⟩ := M.2 v
    exact ⟨e, heM, (mem_iff_incident G hG v e).2 hie⟩
  · funext e
    by_cases h : e ∈ M.1 <;> simp [OAI.MatchingEntropy.LooplessGraph.indicator, charVec, h]

end CombOpt.MatchingPolytope.P816

open CombOpt.MatchingPolytope in
theorem solution {V E : Type*} [Fintype V] [Fintype E] (G : CombOpt.MatchingPolytope.Graph V E)
    (hG : G.IsLoopless) :
    convexHull ℝ {x | ∃ M : Finset E, G.IsPerfectMatching M ∧ x = charVec M} = G.system63 := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (P816.system63_convex G)
    rintro _ ⟨M, hM, rfl⟩
    exact P816.charVec_mem G hG M hM
  · exact P816.system63_subset G hG
