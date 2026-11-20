-- Prove2me | solution 1 for EF104AcyclicPairedOrdering__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T15:15:06.275856+00:00
-- url     : https://prove2.me/submissions/2a5cd512-d461-48b9-877e-9cc5ff084449

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Finset.Sort

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (N : Finset ι) (σ : Equiv.Perm ι)
    (hσ : ∀ i, i ∈ N ↔ σ i ∈ N) (R : ι → ι → Prop)
    (hacyc : ∀ i, ¬ Relation.TransGen R i i) :
    ∃ g ∈ guesses N,
      (∀ p ∈ g.1.zip g.2, p.1 ∈ N ∧ p.2 = σ p.1) ∧
      ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
        g.1.zip g.2 = before ++ p :: after →
        (∃ i ∈ N, R i p.1) → ∃ q ∈ before, R q.1 p.1 := by
  classical
  -- Reachability is antisymmetric because a pair of nontrivial opposite paths is a cycle.
  letI : IsPartialOrder ι (Relation.ReflTransGen R) := {
    refl := fun _ ↦ Relation.ReflTransGen.refl
    trans := fun _ _ _ hab hbc ↦ hab.trans hbc
    antisymm := by
      intro a b hab hba
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with heq | hab
      · exact heq.symm
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp hba with heq | hba
      · exact heq
      · exact (hacyc a (hab.trans hba)).elim
  }
  obtain ⟨s, hs, hreach⟩ := extend_partialOrder (Relation.ReflTransGen R)
  letI : IsLinearOrder ι s := hs
  let l := N.sort s
  have hlmem : ∀ i, i ∈ l ↔ i ∈ N := fun i ↦ Finset.mem_sort s
  have hlnodup : l.Nodup := N.sort_nodup s
  have hlpair : l.Pairwise s := N.pairwise_sort s
  have hlperm : l.Perm N.toList := N.sort_perm_toList s
  have hmperm : (l.map σ).Perm N.toList := by
    apply (List.perm_ext_iff_of_nodup (hlnodup.map σ.injective) N.nodup_toList).mpr
    intro a
    constructor
    · intro ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact Finset.mem_toList.mpr ((hσ i).mp ((hlmem i).mp hi))
    · intro ha
      refine List.mem_map.mpr ⟨σ.symm a, ?_, σ.apply_symm_apply a⟩
      apply (hlmem _).mpr
      apply (hσ (σ.symm a)).mpr
      simpa only [σ.apply_symm_apply] using (Finset.mem_toList.mp ha)
  have hzip : ∀ t : List ι,
      t.zip (t.map σ) = t.map (fun i ↦ (i, σ i)) := by
    intro t
    induction t with
    | nil => rfl
    | cons a t ih => simp only [List.map_cons, List.zip_cons_cons, ih]
  have hzpair : (l.zip (l.map σ)).Pairwise (fun p q ↦ s p.1 q.1) := by
    rw [hzip, List.pairwise_map]
    exact hlpair
  refine ⟨(l, l.map σ), ?_, ?_, ?_⟩
  · change (l, l.map σ) ∈ N.toList.permutations.product N.toList.permutations
    exact List.mem_product.mpr
      ⟨List.mem_permutations.mpr hlperm, List.mem_permutations.mpr hmperm⟩
  · intro p hp
    change p ∈ l.zip (l.map σ) at hp
    rw [hzip] at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact ⟨(hlmem i).mp hi, rfl⟩
  · intro before p after heq hincoming
    change l.zip (l.map σ) = before ++ p :: after at heq
    obtain ⟨i, hiN, hiR⟩ := hincoming
    have hi : i ∈ l := (hlmem i).mpr hiN
    have hipair : (i, σ i) ∈ l.zip (l.map σ) := by
      rw [hzip]
      exact List.mem_map.mpr ⟨i, hi, rfl⟩
    rw [heq, List.mem_append, List.mem_cons] at hipair
    rcases hipair with hbefore | hequal | hafter
    · exact ⟨(i, σ i), hbefore, hiR⟩
    · have hieq : i = p.1 := congrArg Prod.fst hequal
      have hloop : R i i := by simpa only [← hieq] using hiR
      exact (hacyc i (Relation.TransGen.single hloop)).elim
    · have hsorted : (before ++ p :: after).Pairwise (fun x y ↦ s x.1 y.1) := by
        rw [← heq]
        exact hzpair
      have htail := (List.pairwise_append.mp hsorted).2.1
      have hpi : s p.1 i := (List.pairwise_cons.mp htail).1 (i, σ i) hafter
      have hip : s i p.1 := hreach i p.1 (Relation.ReflTransGen.single hiR)
      have hieq : i = p.1 := antisymm_of s hip hpi
      have hloop : R i i := by simpa only [← hieq] using hiR
      exact (hacyc i (Relation.TransGen.single hloop)).elim
