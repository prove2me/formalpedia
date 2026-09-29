-- Prove2me | solution 1 for FranklKupavskii2022.EMC.restricted_shadow_layer
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:29:45.505914+00:00
-- url     : https://prove2.me/submissions/9640b9ff-5399-4fa0-86e6-2e5438277868

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_resShadow

open FinsetFamily

namespace FranklKupavskii2022.EMC

lemma aux_rsl_iF_spec (s k i : ℕ) (F : Finset ℕ) (h : iF s k F = i) (hi : 1 ≤ i) :
    i + 1 ≤ (F ∩ Finset.Icc 1 (i * (s + 1) - 1)).card := by
  unfold iF at h
  set S := (Finset.Ico 1 k).filter
    (fun i => i + 1 ≤ (F ∩ Finset.Icc 1 (i * (s + 1) - 1)).card) with hS
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hS0
    rw [hS0] at h
    simp at h
    omega
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup S hne id
  rw [hjeq] at h
  simp only [id] at h
  subst h
  exact (Finset.mem_filter.1 hj).2

lemma aux_rsl_iF_max (s k j : ℕ) (F : Finset ℕ) (hj1 : 1 ≤ j) (hjk : j < k)
    (h : j + 1 ≤ (F ∩ Finset.Icc 1 (j * (s + 1) - 1)).card) : j ≤ iF s k F := by
  unfold iF
  have hmem : j ∈ (Finset.Ico 1 k).filter
      (fun i => i + 1 ≤ (F ∩ Finset.Icc 1 (i * (s + 1) - 1)).card) := by
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hj1, hjk⟩, h⟩
  exact Finset.le_sup (f := id) hmem

lemma aux_rsl_decomp (F F' : Finset ℕ) (hsub : F' ⊆ F) (hc : F.card = F'.card + 1) :
    ∃ x, x ∉ F' ∧ F = insert x F' := by
  have h1 : (F \ F').card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]; omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
  have hxF : x ∈ F \ F' := by rw [hx]; exact Finset.mem_singleton_self x
  refine ⟨x, (Finset.mem_sdiff.1 hxF).2, ?_⟩
  rw [← Finset.union_sdiff_of_subset hsub, hx]
  ext y; simp

lemma aux_rsl_card_insert_inter (x : ℕ) (F' A : Finset ℕ) (hx : x ∉ F') (hxA : x ∈ A) :
    ((insert x F') ∩ A).card = (F' ∩ A).card + 1 := by
  rw [Finset.insert_inter_of_mem hxA, Finset.card_insert_of_notMem]
  intro h
  exact hx (Finset.mem_inter.1 h).1

lemma aux_rsl_mem_Icc_of_not_tail (s k : ℕ) (F F' : Finset ℕ) (x : ℕ) (hxF : x ∈ F)
    (hxF' : x ∉ F') (ht : tail s k F ⊆ F') :
    x ∈ Finset.Icc 1 (iF s k F * (s + 1) - 1) := by
  by_contra hc
  exact hxF' (ht (Finset.mem_sdiff.2 ⟨hxF, hc⟩))

lemma aux_rsl_layer_card (m k s i : ℕ) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard k) (F : Finset ℕ) (hF : F ∈ layer s k G i) :
    F.card = k ∧ iF s k F = i := by
  unfold layer at hF
  rw [Finset.mem_filter] at hF
  exact ⟨(Finset.mem_powersetCard.1 (hG hF.1)).2, hF.2⟩

lemma aux_rsl_struct (m k s i : ℕ) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard k) (F' : Finset ℕ)
    (hF' : F' ∈ resShadow s k (layer s k G i)) :
    F'.card + 1 = k ∧ ∃ F, F ∈ layer s k G i ∧ iF s k F = i ∧ ∃ x, x ∉ F' ∧ F = insert x F' ∧
      x ∈ Finset.Icc 1 (i * (s + 1) - 1) := by
  unfold resShadow at hF'
  rw [Finset.mem_filter] at hF'
  obtain ⟨hsh, F, hF, ht, hsub⟩ := hF'
  obtain ⟨F0, hF0, hsub0, hc0⟩ := Finset.mem_shadow_iff_exists_mem_card_add_one.1 hsh
  obtain ⟨hk0, _⟩ := aux_rsl_layer_card m k s i G hG F0 hF0
  obtain ⟨hk, hi⟩ := aux_rsl_layer_card m k s i G hG F hF
  refine ⟨by omega, F, hF, hi, ?_⟩
  obtain ⟨x, hx, hFx⟩ := aux_rsl_decomp F F' hsub (by omega)
  refine ⟨x, hx, hFx, ?_⟩
  have := aux_rsl_mem_Icc_of_not_tail s k F F' x (by rw [hFx]; exact Finset.mem_insert_self x F')
    hx ht
  rwa [hi] at this

lemma aux_rsl_res_lower (m k s i : ℕ) (hi : 1 ≤ i) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard k) (F' : Finset ℕ)
    (hF' : F' ∈ resShadow s k (layer s k G i)) :
    i ≤ (F' ∩ Finset.Icc 1 (i * (s + 1) - 1)).card := by
  obtain ⟨_, F, _, hiF, x, hx, hFx, hxI⟩ := aux_rsl_struct m k s i G hG F' hF'
  have h1 := aux_rsl_iF_spec s k i F hiF hi
  rw [hFx, aux_rsl_card_insert_inter x F' _ hx hxI] at h1
  omega

lemma aux_rsl_disj (m k s i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Finset.Icc 1 m).powersetCard k) (F' : Finset ℕ)
    (h1 : F' ∈ resShadow s k (layer s k G i)) (h2 : F' ∈ resShadow s k (layer s k G j)) :
    False := by
  have hlow := aux_rsl_res_lower m k s j (by omega) G hG F' h2
  obtain ⟨_, F, _, hiF, x, hx, hFx, hxI⟩ := aux_rsl_struct m k s i G hG F' h1
  have hIJ : Finset.Icc 1 (i * (s + 1) - 1) ⊆ Finset.Icc 1 (j * (s + 1) - 1) := by
    apply Finset.Icc_subset_Icc le_rfl
    have : i * (s + 1) ≤ j * (s + 1) := Nat.mul_le_mul_right _ hij.le
    omega
  have hc := aux_rsl_card_insert_inter x F' (Finset.Icc 1 (j * (s + 1) - 1)) hx (hIJ hxI)
  rw [← hFx] at hc
  have := aux_rsl_iF_max s k j F (by omega) hjk (by omega)
  omega

end FranklKupavskii2022.EMC

open FranklKupavskii2022.EMC

theorem solution (m k s : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard k) (hinit : IsInitial m k G)
    (hν : matchingNumber (∂ G) ≤ s) :
    (∀ i, 1 ≤ i → i < k →
        ((i : ℝ) + 1) / ((i : ℝ) * s) * ((layer s k G i).card : ℝ) ≤
          ((resShadow s k (layer s k G i)).card : ℝ)) ∧
      ∀ i j, 1 ≤ i → i < k → 1 ≤ j → j < k → i ≠ j →
        Disjoint (resShadow s k (layer s k G i)) (resShadow s k (layer s k G j)) := by
  refine ⟨?_, ?_⟩
  · intro i hi hik
    have key : (layer s k G i).card * (i + 1) ≤ (resShadow s k (layer s k G i)).card * (i * s) := by
      apply Finset.card_mul_le_card_mul
        (fun (F F' : Finset ℕ) => F' ⊆ F ∧ tail s k F ⊆ F' ∧ F.card = F'.card + 1)
      · intro F hF
        obtain ⟨hFk, hiF⟩ := aux_rsl_layer_card m k s i G hG F hF
        have hsp := aux_rsl_iF_spec s k i F hiF hi
        have hsub : (F ∩ (Finset.Icc 1 (i * (s + 1) - 1))).image (fun x => F.erase x) ⊆
            (resShadow s k (layer s k G i)).bipartiteAbove
              (fun (F F' : Finset ℕ) => F' ⊆ F ∧ tail s k F ⊆ F' ∧ F.card = F'.card + 1) F := by
          intro F' hF'
          rw [Finset.mem_image] at hF'
          obtain ⟨x, hx, rfl⟩ := hF'
          have hxF : x ∈ F := (Finset.mem_inter.1 hx).1
          have hxI : x ∈ (Finset.Icc 1 (i * (s + 1) - 1)) := (Finset.mem_inter.1 hx).2
          have htail : tail s k F ⊆ F.erase x := by
            intro y hy
            unfold tail at hy
            rw [Finset.mem_sdiff] at hy
            rw [Finset.mem_erase]
            refine ⟨?_, hy.1⟩
            rintro rfl
            apply hy.2
            rw [hiF]
            exact hxI
          rw [Finset.mem_bipartiteAbove]
          refine ⟨?_, Finset.erase_subset x F, htail, ?_⟩
          · unfold resShadow
            rw [Finset.mem_filter]
            exact ⟨Finset.erase_mem_shadow hF hxF, F, hF, htail, Finset.erase_subset x F⟩
          · rw [Finset.card_erase_of_mem hxF]
            have : 1 ≤ F.card := Finset.card_pos.2 ⟨x, hxF⟩
            omega
        have hcard : ((F ∩ (Finset.Icc 1 (i * (s + 1) - 1))).image (fun x => F.erase x)).card = (F ∩ (Finset.Icc 1 (i * (s + 1) - 1))).card := by
          apply Finset.card_image_of_injOn
          intro x hx y hy hxy
          exact Finset.erase_injOn F (Finset.mem_inter.1 hx).1 (Finset.mem_inter.1 hy).1 hxy
        have := Finset.card_le_card hsub
        omega
      · intro F' hF'
        have hlow := aux_rsl_res_lower m k s i hi G hG F' hF'
        have hsub : (layer s k G i).bipartiteBelow
              (fun (F F' : Finset ℕ) => F' ⊆ F ∧ tail s k F ⊆ F' ∧ F.card = F'.card + 1) F' ⊆
            ((Finset.Icc 1 (i * (s + 1) - 1)) \ F').image (fun y => insert y F') := by
          intro F hF
          rw [Finset.mem_bipartiteBelow] at hF
          obtain ⟨hFL, hsubF, ht, hc⟩ := hF
          obtain ⟨_, hiF⟩ := aux_rsl_layer_card m k s i G hG F hFL
          obtain ⟨x, hx, hFx⟩ := aux_rsl_decomp F F' hsubF hc
          have hxI := aux_rsl_mem_Icc_of_not_tail s k F F' x
            (by rw [hFx]; exact Finset.mem_insert_self x F') hx ht
          rw [hiF] at hxI
          rw [Finset.mem_image]
          exact ⟨x, Finset.mem_sdiff.2 ⟨hxI, hx⟩, hFx.symm⟩
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_image_le (s := (Finset.Icc 1 (i * (s + 1) - 1)) \ F') (f := fun y => insert y F')
        have h3 := Finset.card_sdiff_add_card_inter (Finset.Icc 1 (i * (s + 1) - 1)) F'
        have h4 : (Finset.Icc 1 (i * (s + 1) - 1)).card = i * (s + 1) - 1 := by
          rw [Nat.card_Icc]; omega
        rw [Finset.inter_comm] at h3
        have h5 : i * (s + 1) = i * s + i := by ring
        omega
    have hpos : (0 : ℝ) < (i : ℝ) * s := by
      apply mul_pos
      · exact_mod_cast (show 0 < i by omega)
      · exact_mod_cast (show 0 < s by omega)
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have := (Nat.cast_le (α := ℝ)).mpr key
    push_cast at this
    linarith
  · intro i j hi hik hj hjk hij
    rw [Finset.disjoint_left]
    intro F' h1 h2
    rcases lt_or_gt_of_ne hij with h | h
    · exact aux_rsl_disj m k s i j hi h hjk G hG F' h1 h2
    · exact aux_rsl_disj m k s j i hj h hik G hG F' h2 h1
