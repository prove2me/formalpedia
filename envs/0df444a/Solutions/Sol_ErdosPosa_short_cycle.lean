-- Prove2me | solution 1 for ErdosPosa.short_cycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:28:58.854688+00:00
-- url     : https://prove2.me/submissions/7bd402f5-01dd-4213-b160-369bd20263cb

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Definitions.Def_ErdosPosaLib_EPShort
public import Theorems.Thm_ErdosPosa_suppress_adj
public import Theorems.Thm_ErdosPosa_cyc_suppress_lift
public import Theorems.Thm_ErdosPosa_deg_suppress
public import Theorems.Thm_ErdosPosa_deg_pos_of_adj
public import Theorems.Thm_ErdosPosa_cyc_of_walk
public import Theorems.Thm_ErdosPosa_moore
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Finite V] : ∀ (H : SimpleGraph V),
    (∀ v, deg H v = 0 ∨ deg H v = 2 ∨ deg H v = 3) → ∀ m : ℕ, {v | deg H v = 3}.ncard ≤ m →
    (∃ u w, H.Adj u w) →
    ∃ S, Cyc H S ∧ {v | v ∈ S ∧ deg H v = 3}.ncard ≤ 2 * Nat.log 2 m + 3 := by
  intro H
  induction hn : {v | deg H v = 2}.ncard using Nat.strong_induction_on generalizing H with
  | _ n ih =>
  intro hdeg m hm hedge
  by_cases h2 : ∃ x, deg H x = 2
  · obtain ⟨x, hx⟩ := h2
    obtain ⟨a, b, hab, hN⟩ := Set.ncard_eq_two.1 hx
    have hxa : H.Adj x a := by
      have : a ∈ H.neighborSet x := by rw [hN]; exact Set.mem_insert _ _
      exact this
    have hxb : H.Adj x b := by
      have : b ∈ H.neighborSet x := by rw [hN]; exact Set.mem_insert_of_mem _ rfl
      exact this
    by_cases habj : H.Adj a b
    · refine ⟨{x, a, b}, ?_, ?_⟩
      · let W : H.Walk x a := Walk.cons hxb (Walk.cons habj.symm Walk.nil)
        refine cyc_of_walk hxa W ?_ ?_
        · intro y hy
          simp only [W, Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl <;> simp
        · simp only [W, Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
            or_false, not_or]
          refine ⟨?_, ?_⟩
          · intro he; rw [Sym2.eq_iff] at he
            rcases he with ⟨-, h1⟩ | ⟨h1, -⟩
            · exact hab h1
            · exact hxb.ne h1
          · intro he; rw [Sym2.eq_iff] at he
            rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hxb.ne h1
            · exact hxa.ne h1
      · calc {v | v ∈ ({x, a, b} : Set V) ∧ deg H v = 3}.ncard ≤ ({a, b} : Set V).ncard := by
              apply Set.ncard_le_ncard _ (Set.toFinite _)
              rintro v ⟨hv, hv3⟩
              rcases hv with rfl | hv
              · omega
              · exact hv
          _ ≤ 2 := Set.ncard_pair hab |>.le
          _ ≤ _ := by omega
    · let H' := suppress H x a b
      have hd' := deg_suppress hN hab habj
      have hdeg' : ∀ v, deg H' v = 0 ∨ deg H' v = 2 ∨ deg H' v = 3 := by
        intro v; rw [hd' v]; split_ifs
        · exact Or.inl rfl
        · exact hdeg v
      have h3eq : {v | deg H' v = 3} = {v | deg H v = 3} := by
        ext v
        change deg H' v = 3 ↔ deg H v = 3
        rw [hd' v]; split_ifs with h
        · subst h; simp [hx]
        · rfl
      have h2eq : {v | deg H' v = 2} = {v | deg H v = 2} \ {x} := by
        ext v
        change deg H' v = 2 ↔ (deg H v = 2 ∧ ¬ v ∈ ({x} : Set V))
        rw [hd' v, Set.mem_singleton_iff]; split_ifs with h <;> simp [h]
      have hlt : {v | deg H' v = 2}.ncard < n := by
        rw [h2eq, ← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem hx (Set.toFinite _)
      have hedge' : ∃ u w, H'.Adj u w := ⟨a, b, suppress_adj.2 (Or.inr (Or.inl ⟨rfl, rfl, hab⟩))⟩
      obtain ⟨S', hS', hcnt⟩ := ih _ hlt H' rfl hdeg' m (h3eq ▸ hm) hedge'
      refine ⟨insert x S', cyc_suppress_lift hxa hxb hS', ?_⟩
      convert hcnt using 2
      ext v
      change (v ∈ insert x S' ∧ deg H v = 3) ↔ (v ∈ S' ∧ deg H' v = 3)
      rw [hd' v, Set.mem_insert_iff]
      by_cases h : v = x
      · subst h; simp [hx]
      · simp [h]
  · push Not at h2
    obtain ⟨u, w, huw⟩ := hedge
    have hdeg3 : ∀ v, deg H v ≠ 0 → deg H v = 3 := by
      intro v hv
      rcases hdeg v with h | h | h
      · exact absurd h hv
      · exact absurd h (h2 v)
      · exact h
    have hreach3 : ∀ y, H.Reachable u y → 3 ≤ deg H y := by
      intro y hy
      by_cases hyu : y = u
      · subst hyu; rw [hdeg3 y (deg_pos_of_adj huw).ne']
      · obtain ⟨p⟩ := hy.symm
        have hnil : ¬ p.Nil := by
          rw [← Walk.length_eq_zero_iff]
          intro hl
          exact hyu (Walk.eq_of_length_eq_zero hl)
        rw [hdeg3 y (deg_pos_of_adj (p.adj_snd hnil)).ne']
    by_contra hcon
    push Not at hcon
    have hno : ∀ S : Set V, S.ncard ≤ 2 * (Nat.log 2 m + 1) + 1 → ¬ Cyc H S := by
      intro S hS hc
      have := hcon S hc
      have : {v | v ∈ S ∧ deg H v = 3}.ncard ≤ S.ncard :=
        Set.ncard_le_ncard (fun v hv => hv.1) (Set.toFinite _)
      omega
    have hM := moore u _ hreach3 hno
    have hsub : {x | H.Reachable u x ∧ H.dist u x = Nat.log 2 m + 1} ⊆ {v | deg H v = 3} := by
      intro y hy
      have := hreach3 y hy.1
      exact hdeg3 y (by omega)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    omega
end ErdosPosa
