-- Prove2me | solution 1 for CliqueMinors.DiracCtx.op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:17.140798+00:00
-- url     : https://prove2.me/submissions/185cf859-76eb-453e-98ca-68563ae7b07d

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_lift_contract
public import Theorems.Thm_CliqueMinors_opG_adj


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
open CliqueMinors.DiracCtx
variable {G : SimpleGraph V} {S : Finset V}
namespace CliqueMinors.DiracCtx
theorem _root_.solution (H : DiracCtx G S) {x a b c : V}
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c)
    (hb : ∀ t, G.Adj b t → t = x ∨ t = a ∨ t = c)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : ¬ G.Adj a c) (hac' : a ≠ c)
    (ha4 : 4 ≤ G.degree a) (hc4 : 4 ≤ G.degree c) : False := by
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  have hxc : G.Adj x c := (hx c).2 (Or.inr (Or.inr rfl))
  apply H.notK4
  refine isMinor_lift_contract (G' := opG G x b a c) (x := a) (y := x) hxa.symm
    (fun u v h => ?_) (by omega) ?_
  · obtain ⟨_, hux, _, hvx, _, h⟩ := opG_adj.1 h
    refine ⟨hux, hvx, ?_⟩
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, hxc⟩)
    · exact Or.inr (Or.inr ⟨rfl, hxc⟩)
  have hxS : x ∈ S := H.supp _ _ hxa
  have hbS : b ∈ S := H.supp _ _ hab.symm
  have hbx : b ≠ x := hxb.ne.symm
  have hS3 : ((S.erase x).erase b).card < S.card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hbx, hbS⟩), Finset.card_erase_of_mem hxS]
    have := Finset.card_pos.2 ⟨x, hxS⟩
    omega
  refine H.smaller _ ((S.erase x).erase b) hS3
    ⟨a, by simp [hab.ne, hxa.ne.symm, H.supp _ _ hab]⟩ (fun u v h => ?_) (fun v hv => ?_)
  · obtain ⟨_, hux, hub, _, _, h⟩ := opG_adj.1 h
    simp only [Finset.mem_erase]
    refine ⟨hub, hux, ?_⟩
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact H.supp _ _ h
    · exact H.supp _ _ hab
    · exact H.supp _ _ hbc.symm
  · simp only [Finset.mem_erase] at hv
    obtain ⟨hvb, hvx, hvS⟩ := hv
    have key : ∀ e e', (e = a ∧ e' = c ∨ e = c ∧ e' = a) → 4 ≤ G.degree e → G.Adj x e →
        G.Adj b e → ¬ G.Adj e e' → e ≠ e' → 3 ≤ (opG G x b a c).degree e := by
      intro e e' hee' he4 hxe hbe hne hne'
      have hsub : insert e' (((G.neighborFinset e).erase x).erase b) ⊆
          (opG G x b a c).neighborFinset e := by
        refine Finset.insert_subset ?_ fun t ht => ?_
        · rw [mem_neighborFinset, opG_adj]
          refine ⟨hne', hxe.ne.symm, hbe.ne.symm, ?_, ?_, Or.inr hee'⟩
          · rintro rfl; exact hne hxe.symm
          · rintro rfl; exact hne hbe.symm
        · simp only [Finset.mem_erase, mem_neighborFinset] at ht
          rw [mem_neighborFinset, opG_adj]
          exact ⟨ht.2.2.ne, hxe.ne.symm, hbe.ne.symm, ht.2.1, ht.1, Or.inl ht.2.2⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [hne]),
        Finset.card_erase_of_mem (by simp [hbe.symm, hbx]),
        Finset.card_erase_of_mem (by simpa using hxe.symm), card_neighborFinset_eq_degree,
        card_neighborFinset_eq_degree] at h1
      omega
    by_cases hva : v = a
    · subst hva
      exact key v c (Or.inl ⟨rfl, rfl⟩) ha4 hxa hab.symm hac hac'
    by_cases hvc : v = c
    · subst hvc
      exact key v a (Or.inr ⟨rfl, rfl⟩) hc4 hxc hbc (fun h => hac h.symm) hac'.symm
    refine (H.deg v hvS).trans ?_
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    refine Finset.card_le_card fun t ht => ?_
    rw [mem_neighborFinset] at ht
    rw [mem_neighborFinset, opG_adj]
    refine ⟨ht.ne, hvx, hvb, ?_, ?_, Or.inl ht⟩
    · rintro rfl
      rcases (hx v).1 ht.symm with h | h | h <;> contradiction
    · rintro rfl
      rcases hb v ht.symm with h | h | h <;> contradiction
end CliqueMinors.DiracCtx
