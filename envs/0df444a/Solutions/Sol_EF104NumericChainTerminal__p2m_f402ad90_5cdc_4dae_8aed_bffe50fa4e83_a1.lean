-- Prove2me | solution 1 for EF104NumericChainTerminal__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:34:27.518829+00:00
-- url     : https://prove2.me/submissions/e578a2cc-a67c-4f3b-a6da-d4f9be389721

import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.List
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Common
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise


namespace NCTAux

/-- A simple cycle of a relation supported in a finite set, from a `TransGen` loop. -/
theorem simple_cycle {ι : Type} [DecidableEq ι] (N : Finset ι) (R : ι → ι → Prop)
    (hR : ∀ a b, R a b → a ∈ N) (i : ι) (h : Relation.TransGen R i i) :
    ∃ l : List ι, l.Nodup ∧ l ≠ [] ∧ (∀ a ∈ l, a ∈ N) ∧ ∀ a ∈ l, R a (l.formPerm a) := by
  classical
  let S : ι → Prop := fun a => Relation.TransGen R a a
  have hnext : ∀ a, S a → ∃ b, R a b ∧ S b := by
    intro a ha
    obtain ⟨b, hab, hba⟩ := Relation.TransGen.head'_iff.mp ha
    exact ⟨b, hab, Relation.TransGen.tail' hba hab⟩
  let f : ι → ι := fun a => if h : S a then Classical.choose (hnext a h) else a
  have hf : ∀ a, S a → R a (f a) ∧ S (f a) := by
    intro a ha
    simp only [f, dif_pos ha]
    exact Classical.choose_spec (hnext a ha)
  have hS : ∀ n, S (f^[n] i) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hf _ ih).2
  have hSN : ∀ a, S a → a ∈ N := by
    intro a ha
    obtain ⟨b, hab, -⟩ := Relation.TransGen.head'_iff.mp ha
    exact hR a b hab
  -- pigeonhole on the orbit
  let F : ℕ → N := fun n => ⟨f^[n] i, hSN _ (hS n)⟩
  obtain ⟨p, q, hpq, hFpq⟩ : ∃ p q, p ≠ q ∧ F p = F q := by
    have := not_injective_infinite_finite F
    simp only [Function.Injective, not_forall] at this
    obtain ⟨p, q, h1, h2⟩ := this
    exact ⟨p, q, h2, h1⟩
  have hfeq : f^[p] i = f^[q] i := congrArg Subtype.val hFpq
  wlog hlt : p < q generalizing p q
  · exact this q p (Ne.symm hpq) hFpq.symm hfeq.symm (by omega)
  set c := f^[p] i with hc
  have hper : Function.IsPeriodicPt f (q - p) c := by
    show f^[q - p] (f^[p] i) = f^[p] i
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact hfeq.symm
  have hL : 0 < Function.minimalPeriod f c := hper.minimalPeriod_pos (by omega)
  set L := Function.minimalPeriod f c with hLdef
  have hSc : ∀ n, S (f^[n] c) := by
    intro n; rw [hc, ← Function.iterate_add_apply]; exact hS _
  let l : List ι := (List.range L).map (fun n => f^[n] c)
  have hlen : l.length = L := by simp [l]
  have hget : ∀ n (h : n < l.length), l[n] = f^[n] c := by
    intro n h; simp [l]
  have hnd : l.Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro a ha b hb hab
    rw [List.mem_range] at ha hb
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod ha hb).mp hab
  refine ⟨l, hnd, ?_, ?_, ?_⟩
  · intro hl; rw [hl] at hlen; simp at hlen; omega
  · intro a ha
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact hSN _ (hSc n)
  · intro a ha
    obtain ⟨n, hn, hnl⟩ := List.getElem_of_mem ha
    rw [← hnl, List.formPerm_apply_getElem l hnd n hn, hget, hget, hlen,
      (Function.isPeriodicPt_minimalPeriod f c).iterate_mod_apply, Function.iterate_succ_apply']
    exact (hf _ (hSc n)).1

end NCTAux

open NCTAux in
theorem solution
    {ι : Type} [DecidableEq ι] (N : Finset ι) (hN : N.Nonempty)
    (m : ι → ℕ) (u : ι → ι → ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ i ∈ N, ∀ j ∈ N, u i j 0 = 0)
    (hstep : ∀ j ∈ N, ∀ k < m j, ∀ i ∈ N,
      0 ≤ u i j (k + 1) - u i j k ∧ u i j (k + 1) - u i j k ≤ δ) :
    ∃ σ : Equiv.Perm ι, (∀ i, i ∈ N ↔ σ i ∈ N) ∧
      ∃ k : ι → ℕ,
        (∀ i ∈ N, k i ≤ m (σ i)) ∧
        (∀ i ∈ N, ∀ j ∈ N,
          u i (σ j) (k j) ≤ u i (σ i) (k i) + δ) ∧
        (∀ i, ¬ Relation.TransGen
          (fun a b ↦ a ∈ N ∧ b ∈ N ∧ u a (σ a) (k a) < u a (σ b) (k b)) i i) ∧
        ∀ j ∈ N, k j = m (σ j) ∨
          ∃ i ∈ N, u i (σ i) (k i) < u i (σ j) (k j) := by
  -- monotonicity of the chains
  have mono : ∀ i ∈ N, ∀ j ∈ N, ∀ a b, a ≤ b → b ≤ m j → u i j a ≤ u i j b := by
    intro i hi j hj a b hab hb
    induction b with
    | zero => rw [Nat.le_zero.mp hab]
    | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · have := (hstep j hj b (by omega) i hi).1
        linarith [ih (by omega) (by omega)]
      · rw [show a = b + 1 by omega]
  let Good0 : Equiv.Perm ι → (ι → ℕ) → Prop := fun σ k =>
    (∀ i, i ∈ N ↔ σ i ∈ N) ∧ (∀ i ∈ N, k i ≤ m (σ i)) ∧
      ∀ i ∈ N, ∀ j ∈ N, u i (σ j) (k j) ≤ u i (σ i) (k i) + δ
  let D : Equiv.Perm ι → (ι → ℕ) → ℕ := fun σ k => ∑ j ∈ N, (m (σ j) - k j)
  let E : Equiv.Perm ι → (ι → ℕ) → ℕ := fun σ k =>
    ∑ a ∈ N, (N.filter (fun b => u a (σ a) (k a) < u a (σ b) (k b))).card
  -- growing an unenvied bundle
  have inc : ∀ σ k, Good0 σ k → ∀ j ∈ N, k j < m (σ j) →
      (∀ i ∈ N, ¬ u i (σ i) (k i) < u i (σ j) (k j)) →
      Good0 σ (Function.update k j (k j + 1)) ∧ D σ (Function.update k j (k j + 1)) < D σ k := by
    intro σ k ⟨hσ, hk, hEF⟩ j hj hkj hun
    have hσj : σ j ∈ N := (hσ j).1 hj
    refine ⟨⟨hσ, ?_, ?_⟩, ?_⟩
    · intro i hi
      by_cases hij : i = j
      · subst hij; simp; omega
      · rw [Function.update_of_ne hij]; exact hk i hi
    · intro i hi j' hj'
      have hσi : σ i ∈ N := (hσ i).1 hi
      have hσj' : σ j' ∈ N := (hσ j').1 hj'
      by_cases hj'j : j' = j
      · subst hj'j
        by_cases hij : i = j'
        · subst hij; simp; linarith
        · rw [Function.update_of_ne hij, Function.update_self]
          have h1 := (hstep (σ j') hσj (k j') hkj i hi).2
          have h2 := not_lt.mp (hun i hi)
          linarith
      · rw [Function.update_of_ne hj'j]
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self]
          have h1 := hEF i hi j' hj'
          have h2 := mono i hi (σ i) hσi (k i) (k i + 1) (by omega) (by omega)
          linarith
        · rw [Function.update_of_ne hij]; exact hEF i hi j' hj'
    · apply Finset.sum_lt_sum
      · intro j' _
        by_cases hj'j : j' = j
        · subst hj'j; simp; omega
        · rw [Function.update_of_ne hj'j]
      · exact ⟨j, hj, by simp; omega⟩
  -- rotating along an envy cycle
  have rot : ∀ σ k, Good0 σ k → ∀ i, Relation.TransGen
      (fun a b ↦ a ∈ N ∧ b ∈ N ∧ u a (σ a) (k a) < u a (σ b) (k b)) i i →
      ∃ σ' k', Good0 σ' k' ∧ D σ' k' = D σ k ∧ E σ' k' < E σ k := by
    intro σ k ⟨hσ, hk, hEF⟩ i hcyc
    obtain ⟨l, hnd, hne, hlN, hlR⟩ := simple_cycle N _ (fun a b h => h.1) i hcyc
    set π := l.formPerm with hπ
    have hπfix : ∀ a, a ∉ l → π a = a := fun a ha => List.formPerm_apply_of_notMem ha
    have hπl : ∀ a, a ∈ l → π a ∈ l := fun a ha => List.formPerm_apply_mem_of_mem ha
    have hπN : ∀ a, a ∈ N ↔ π a ∈ N := by
      intro a
      by_cases ha : a ∈ l
      · exact ⟨fun _ => hlN _ (hπl a ha), fun _ => hlN a ha⟩
      · rw [hπfix a ha]
    have hsupp : {a | π a ≠ a} ⊆ (N : Set ι) := by
      intro a ha
      by_contra hn
      have : a ∉ l := fun hl => hn (hlN a hl)
      exact ha (hπfix a this)
    -- values weakly increase, strictly on the cycle
    let val : ι → ℝ := fun a => u a (σ a) (k a)
    let val' : ι → ℝ := fun a => u a (σ (π a)) (k (π a))
    have hup : ∀ a ∈ N, val a ≤ val' a := by
      intro a ha
      by_cases hal : a ∈ l
      · simp only [val, val', hπ]; exact (hlR a hal).2.2.le
      · simp only [val, val', hπfix a hal]; rfl
    have hstrict : ∀ a ∈ l, val a < val' a := fun a hal => by
      simp only [val, val', hπ]; exact (hlR a hal).2.2
    refine ⟨σ * π, k ∘ π, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro a; rw [Equiv.Perm.mul_apply, hπN a, hσ (π a)]
    · intro a ha; exact hk (π a) ((hπN a).1 ha)
    · intro a ha b hb
      simp only [Equiv.Perm.mul_apply, Function.comp]
      have := hEF a ha (π b) ((hπN b).1 hb)
      have h2 := hup a ha
      simp only [val, val'] at h2
      linarith
    · simp only [D, Equiv.Perm.mul_apply, Function.comp]
      exact Equiv.Perm.sum_comp π N (fun j => m (σ j) - k j) hsupp
    · simp only [E, Equiv.Perm.mul_apply, Function.comp]
      -- reindex the inner filters
      have hre : ∀ a ∈ N, (N.filter (fun b => u a (σ (π a)) (k (π a)) <
            u a (σ (π b)) (k (π b)))).card =
          (N.filter (fun b => val' a < u a (σ b) (k b))).card := by
        intro a _
        rw [Finset.card_filter, Finset.card_filter]
        exact Equiv.Perm.sum_comp π N (fun b => if val' a < u a (σ b) (k b) then 1 else 0) hsupp
      refine lt_of_eq_of_lt (Finset.sum_congr rfl hre) ?_
      obtain ⟨a0, ha0⟩ := List.exists_mem_of_ne_nil l hne
      apply Finset.sum_lt_sum
      · intro a ha
        apply Finset.card_le_card
        intro b hb
        simp only [Finset.mem_filter] at hb ⊢
        exact ⟨hb.1, lt_of_le_of_lt (hup a ha) hb.2⟩
      · refine ⟨a0, hlN a0 ha0, Finset.card_lt_card ⟨?_, ?_⟩⟩
        · intro b hb
          simp only [Finset.mem_filter] at hb ⊢
          exact ⟨hb.1, lt_of_le_of_lt (hup a0 (hlN a0 ha0)) hb.2⟩
        · intro hsub
          have hmem : π a0 ∈ N.filter (fun b => val a0 < u a0 (σ b) (k b)) := by
            simp only [Finset.mem_filter]
            exact ⟨hlN _ (hπl a0 ha0), hstrict a0 ha0⟩
          have := hsub hmem
          simp only [Finset.mem_filter, val', lt_irrefl, and_false] at this
  -- well-founded descent
  have main : ∀ d e, ∀ σ k, Good0 σ k → D σ k = d → E σ k = e →
      ∃ σ : Equiv.Perm ι, (∀ i, i ∈ N ↔ σ i ∈ N) ∧
        ∃ k : ι → ℕ, (∀ i ∈ N, k i ≤ m (σ i)) ∧
          (∀ i ∈ N, ∀ j ∈ N, u i (σ j) (k j) ≤ u i (σ i) (k i) + δ) ∧
          (∀ i, ¬ Relation.TransGen
            (fun a b ↦ a ∈ N ∧ b ∈ N ∧ u a (σ a) (k a) < u a (σ b) (k b)) i i) ∧
          ∀ j ∈ N, k j = m (σ j) ∨ ∃ i ∈ N, u i (σ i) (k i) < u i (σ j) (k j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ihd =>
      intro e
      induction e using Nat.strong_induction_on with
      | _ e ihe =>
        intro σ k hG hD hE
        by_cases hcyc : ∃ i, Relation.TransGen
            (fun a b ↦ a ∈ N ∧ b ∈ N ∧ u a (σ a) (k a) < u a (σ b) (k b)) i i
        · obtain ⟨i, hi⟩ := hcyc
          obtain ⟨σ', k', hG', hD', hE'⟩ := rot σ k hG i hi
          exact ihe _ (hE ▸ hE') σ' k' hG' (hD'.trans hD) rfl
        · push Not at hcyc
          by_cases hterm : ∀ j ∈ N, k j = m (σ j) ∨
              ∃ i ∈ N, u i (σ i) (k i) < u i (σ j) (k j)
          · exact ⟨σ, hG.1, k, hG.2.1, hG.2.2, hcyc, hterm⟩
          · push Not at hterm
            obtain ⟨j, hj, hjm, hun⟩ := hterm
            have hlt : k j < m (σ j) := lt_of_le_of_ne (hG.2.1 j hj) hjm
            obtain ⟨hG', hD'⟩ := inc σ k hG j hj hlt (fun i hi => not_lt.mpr (hun i hi))
            exact ihd _ (hD ▸ hD') _ _ _ hG' rfl rfl
  refine main _ _ 1 (fun _ => 0) ⟨fun i => Iff.rfl, fun i _ => Nat.zero_le _, ?_⟩ rfl rfl
  intro i hi j hj
  simp only [Equiv.Perm.one_apply]
  rw [hzero i hi j hj, hzero i hi i hi]; linarith
