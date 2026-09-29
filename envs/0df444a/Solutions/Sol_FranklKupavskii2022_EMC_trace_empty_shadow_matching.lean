-- Prove2me | solution 1 for FranklKupavskii2022.EMC.trace_empty_shadow_matching
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:44:44.608866+00:00
-- url     : https://prove2.me/submissions/506a3774-c045-4f39-a0df-24568e24bcfc

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_trace

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Replacing an element `x ∉ G` by a smaller element `y ∉ G` lowers the sorted list entrywise. -/
theorem aux_tes_sort (G : Finset ℕ) : ∀ y x : ℕ, y < x → y ∉ G → x ∉ G →
    List.Forall₂ (· ≤ ·) (insert y G).sort (insert x G).sort := by
  induction G using Finset.induction_on_min with
  | empty =>
    intro y x hyx _ _
    simp [Finset.sort_singleton, hyx.le]
  | insert a G' ha ih =>
    intro y x hyx hy hx
    simp only [Finset.mem_insert, not_or] at hy hx
    obtain ⟨hya, hyG⟩ := hy
    obtain ⟨hxa, hxG⟩ := hx
    have haG : a ∉ G' := fun h => lt_irrefl a (ha a h)
    rcases lt_or_gt_of_ne hya with hlt | hlt
    · -- y < a
      have e1 : (insert y (insert a G')).sort = y :: (insert a G').sort := by
        apply Finset.sort_insert
        · intro b hb
          rcases Finset.mem_insert.1 hb with hb | hb
          · rw [hb]; exact hlt.le
          · exact (hlt.trans (ha b hb)).le
        · simp [hya, hyG]
      rw [e1]
      rcases lt_or_gt_of_ne hxa with hxlt | hxlt
      · have e2 : (insert x (insert a G')).sort = x :: (insert a G').sort := by
          apply Finset.sort_insert
          · intro b hb
            rcases Finset.mem_insert.1 hb with hb | hb
            · rw [hb]; exact hxlt.le
            · exact (hxlt.trans (ha b hb)).le
          · simp [hxa, hxG]
        rw [e2]
        exact List.Forall₂.cons hyx.le (List.forall₂_refl _)
      · have e2 : (insert x (insert a G')).sort = a :: (insert x G').sort := by
          rw [Finset.insert_comm]
          apply Finset.sort_insert
          · intro b hb
            rcases Finset.mem_insert.1 hb with hb | hb
            · rw [hb]; exact hxlt.le
            · exact (ha b hb).le
          · simp [Ne.symm hxa, haG]
        rw [e2]
        exact List.Forall₂.cons hlt.le (ih a x hxlt haG hxG)
    · -- a < y
      have hax : a < x := hlt.trans hyx
      have e1 : (insert y (insert a G')).sort = a :: (insert y G').sort := by
        rw [Finset.insert_comm]
        apply Finset.sort_insert
        · intro b hb
          rcases Finset.mem_insert.1 hb with hb | hb
          · rw [hb]; exact hlt.le
          · exact (ha b hb).le
        · simp [Ne.symm hya, haG]
      have e2 : (insert x (insert a G')).sort = a :: (insert x G').sort := by
        rw [Finset.insert_comm]
        apply Finset.sort_insert
        · intro b hb
          rcases Finset.mem_insert.1 hb with hb | hb
          · rw [hb]; exact hax.le
          · exact (ha b hb).le
        · simp [Ne.symm hxa, haG]
      rw [e1, e2]
      exact List.Forall₂.cons le_rfl (ih y x hyx hyG hxG)

theorem aux_tes_main (n k s : ℕ) (hk : 1 ≤ k) (hn : k * (s + 1) ≤ n)
    (F : Finset (Finset ℕ)) (hF : F ⊆ (Finset.Icc 1 n).powersetCard k) (hinit : IsInitial n k F)
    (hν : matchingNumber F ≤ s) (M : Finset (Finset ℕ)) (hM : M ⊆ ∂ (trace s F ∅))
    (hMd : ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B) : M.card ≤ s := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨M', hM'M, hM'c⟩ := Finset.exists_subset_card_eq (show s + 1 ≤ M.card from hlt)
  have hmem : ∀ G ∈ M', ∃ A ∈ F, A ∩ Finset.Icc 1 (s + 1) = ∅ ∧ ∃ x ∈ A, A.erase x = G := by
    intro G hG
    have := hM (hM'M hG)
    rw [Finset.mem_shadow_iff] at this
    obtain ⟨A, hA, x, hx, rfl⟩ := this
    simp only [trace, Finset.sdiff_empty, Finset.image_id', Finset.mem_filter] at hA
    exact ⟨A, hA.1, hA.2, x, hx, rfl⟩
  have hsn : s + 1 ≤ n := le_trans (by nlinarith) hn
  have hlift : ∀ G ∈ M', ∀ i, 1 ≤ i → i ≤ s + 1 →
      insert i G ∈ F ∧ ∀ j, 1 ≤ j → j ≤ s + 1 → j ∉ G := by
    intro G hG i hi1 hi2
    obtain ⟨A, hAF, hAe, x, hx, rfl⟩ := hmem G hG
    have hA := hF hAF
    rw [Finset.mem_powersetCard] at hA
    have hjA : ∀ j, 1 ≤ j → j ≤ s + 1 → j ∉ A := by
      intro j hj1 hj2 hjA
      have : j ∈ A ∩ Finset.Icc 1 (s + 1) :=
        Finset.mem_inter.2 ⟨hjA, Finset.mem_Icc.2 ⟨hj1, hj2⟩⟩
      rw [hAe] at this
      simp at this
    have hxs : s + 1 < x := by
      have := Finset.mem_Icc.1 (hA.1 hx)
      by_contra h
      rw [not_lt] at h
      exact hjA x this.1 h hx
    refine ⟨?_, fun j hj1 hj2 hjG => hjA j hj1 hj2 (Finset.mem_of_mem_erase hjG)⟩
    have hiA : i ∉ A := hjA i hi1 hi2
    have hiG : i ∉ A.erase x := fun h => hiA (Finset.mem_of_mem_erase h)
    apply hinit (insert i (A.erase x)) _ A hAF
    · refine ⟨?_, ?_⟩
      · have := aux_tes_sort (A.erase x) i x (by omega) hiG (Finset.notMem_erase x A)
        rwa [Finset.insert_erase hx] at this
      · intro h
        apply hiA
        rw [← h]
        exact Finset.mem_insert_self _ _
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.1 hz with hz | hz
        · rw [hz]; exact Finset.mem_Icc.2 ⟨hi1, by omega⟩
        · exact hA.1 (Finset.mem_of_mem_erase hz)
      · rw [Finset.card_insert_of_notMem hiG, Finset.card_erase_of_mem hx, hA.2]
        omega
  let e : Fin (s + 1) ≃ M' := (M'.equivFin.trans (finCongr hM'c)).symm
  let g : Fin (s + 1) → Finset ℕ := fun j => (e j).val
  have hg_mem : ∀ j, g j ∈ M' := fun j => (e j).property
  have hg_inj : Function.Injective g := by
    intro a b h
    apply e.injective
    exact Subtype.ext h
  have hfree : ∀ j l : Fin (s + 1), (j.val + 1) ∉ g l := by
    intro j l
    have := j.2
    exact (hlift _ (hg_mem l) 1 le_rfl (by omega)).2 _ (by omega) (by omega)
  let f : Fin (s + 1) → Finset ℕ := fun j => insert (j.val + 1) (g j)
  have hf_inj : Function.Injective f := by
    intro a b h
    have h1 : a.val + 1 ∈ f b := by
      rw [← h]; exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.1 h1 with h2 | h2
    · exact Fin.ext (by omega)
    · exact absurd h2 (hfree a b)
  let N := Finset.univ.image f
  have hNcard : N.card = s + 1 := by
    rw [Finset.card_image_of_injective _ hf_inj]; simp
  have hNmem : N ∈ F.powerset.filter (fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro A hA
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hA
      have := j.2
      exact (hlift _ (hg_mem j) (j.val + 1) (by omega) (by omega)).1
    · intro A hA B hB hAB
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hA
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 hB
      have hjl : j ≠ l := fun h => hAB (by rw [h])
      have hgd : Disjoint (g j) (g l) :=
        hMd _ (hM'M (hg_mem j)) _ (hM'M (hg_mem l)) (fun h => hjl (hg_inj h))
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      rcases Finset.mem_insert.1 hz1 with h1 | h1 <;>
        rcases Finset.mem_insert.1 hz2 with h2 | h2
      · exact hjl (Fin.ext (by omega))
      · rw [h1] at h2; exact hfree j l h2
      · rw [h2] at h1; exact hfree l j h1
      · exact Finset.disjoint_left.1 hgd h1 h2
  have := Finset.le_sup (f := Finset.card) hNmem
  unfold matchingNumber at hν
  omega

end FranklKupavskii2022.EMC

open FranklKupavskii2022.EMC

theorem solution (n k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hn : k * (s + 1) ≤ n)
    (F : Finset (Finset ℕ)) (hF : F ⊆ (Finset.Icc 1 n).powersetCard k) (hinit : IsInitial n k F)
    (hν : matchingNumber F ≤ s) :
    matchingNumber (∂ (trace s F ∅)) ≤ s := by
  unfold matchingNumber
  apply Finset.sup_le
  intro M hM
  rw [Finset.mem_filter, Finset.mem_powerset] at hM
  exact aux_tes_main n k s hk hn F hF hinit hν M hM.1 hM.2
