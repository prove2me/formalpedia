-- Prove2me | solution 1 for EnvyFreeCake104.Divide.guess_order_certificate__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:12:31.369672+00:00
-- url     : https://prove2.me/submissions/8c1646ab-333f-4aa2-9f4b-121acafd2af9

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

theorem solution
    {ι : Type} [DecidableEq ι] (N : Finset ι)
    (g : List ι × List ι) (hg : g ∈ guesses N) :
    g.1.Nodup ∧
    (∀ p ∈ g.1.zip g.2, p.1 ∈ N ∧ p.2 ∈ N) ∧
    ∃ (π : ι → ι) (rank : ι → ℕ),
      Set.BijOn π (N : Set ι) (N : Set ι) ∧
      ∀ i ∈ N, ∃ (before after : List (ι × ι)),
        g.1.zip g.2 = before ++ (i, π i) :: after ∧
        ∀ j ∈ before.map Prod.fst, j ∈ N ∧ rank j < rank i := by
  obtain ⟨l1, l2⟩ := g
  unfold guesses at hg
  rw [List.pair_mem_product, List.mem_permutations, List.mem_permutations] at hg
  obtain ⟨h1, h2⟩ := hg
  simp only
  have hn1 : l1.Nodup := h1.nodup_iff.mpr (Finset.nodup_toList N)
  have hn2 : l2.Nodup := h2.nodup_iff.mpr (Finset.nodup_toList N)
  have hm1 : ∀ x, x ∈ l1 ↔ x ∈ N := fun x => by rw [h1.mem_iff, Finset.mem_toList]
  have hm2 : ∀ x, x ∈ l2 ↔ x ∈ N := fun x => by rw [h2.mem_iff, Finset.mem_toList]
  have hlen : l1.length = l2.length := h1.length_eq.trans h2.length_eq.symm
  refine ⟨hn1, ?_, ?_⟩
  · intro p hp
    have := List.of_mem_zip hp
    exact ⟨(hm1 _).1 this.1, (hm2 _).1 this.2⟩
  let π : ι → ι := fun i => l2.getD (l1.idxOf i) i
  have hπ : ∀ i ∈ N, ∃ h : l1.idxOf i < l2.length, π i = l2[l1.idxOf i] := by
    intro i hi
    have h : l1.idxOf i < l2.length := hlen ▸ List.idxOf_lt_length_of_mem ((hm1 i).2 hi)
    exact ⟨h, by simp [π, List.getD_eq_getElem?_getD, h]⟩
  refine ⟨π, fun i => l1.idxOf i, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨h, e⟩ := hπ i hi
    rw [e]; exact (hm2 _).1 (List.getElem_mem h)
  · intro i hi i' hi' he
    obtain ⟨h, e⟩ := hπ i hi
    obtain ⟨h', e'⟩ := hπ i' hi'
    rw [e, e', hn2.getElem_inj_iff] at he
    have a := List.getElem_idxOf (List.idxOf_lt_length_of_mem ((hm1 i).2 hi))
    have b := List.getElem_idxOf (List.idxOf_lt_length_of_mem ((hm1 i').2 hi'))
    rw [← a, ← b]; simp only [he]
  · intro j hj
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ((hm2 j).2 hj)
    have hk1 : k < l1.length := hlen ▸ hk
    refine ⟨l1[k], (hm1 _).1 (List.getElem_mem hk1), ?_⟩
    obtain ⟨h, e⟩ := hπ _ ((hm1 _).1 (List.getElem_mem hk1))
    rw [e]
    simp only [hn1.idxOf_getElem]
  · intro i hi
    obtain ⟨h, e⟩ := hπ i hi
    set k := l1.idxOf i with hkdef
    have hk1 : k < l1.length := List.idxOf_lt_length_of_mem ((hm1 i).2 hi)
    have hkz : k < (l1.zip l2).length := by simp [List.length_zip]; omega
    refine ⟨(l1.zip l2).take k, (l1.zip l2).drop (k+1), ?_, ?_⟩
    · conv_lhs => rw [← List.take_append_drop k (l1.zip l2)]
      rw [List.drop_eq_getElem_cons hkz, List.getElem_zip, e]
      congr 3
      exact List.getElem_idxOf hk1
    · intro j hj
      rw [List.map_take, List.map_fst_zip (by omega)] at hj
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hj
      rw [List.getElem_take]
      have hmk : m < k := by simp at hm; omega
      have hml : m < l1.length := by omega
      refine ⟨(hm1 _).1 (List.getElem_mem hml), ?_⟩
      simp only [hn1.idxOf_getElem]
      exact hmk
