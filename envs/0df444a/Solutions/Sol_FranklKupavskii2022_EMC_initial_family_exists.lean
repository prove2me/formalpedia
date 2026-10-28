-- Prove2me | solution 1 for FranklKupavskii2022.EMC.initial_family_exists
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T07:06:33.474156+00:00
-- url     : https://prove2.me/submissions/0c0e7a72-4f8f-460f-8064-5d4512a4ff35

import Init
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial

namespace FranklKupavskii2022.EMC.Shifting
open Finset

def swapSet (i j : ℕ) (A : Finset ℕ) : Finset ℕ := A.map (Equiv.swap i j).toEmbedding

theorem swapSet_injective (i j : ℕ) : Function.Injective (swapSet i j) :=
  Finset.map_injective _

theorem swapSet_disjoint (i j : ℕ) (A B : Finset ℕ) :
    Disjoint (swapSet i j A) (swapSet i j B) ↔ Disjoint A B :=
  Finset.disjoint_map _

theorem swapSet_absent (i j : ℕ) (A : Finset ℕ) (hi : i ∉ A) (hj : j ∉ A) :
    swapSet i j A = A := by
  ext x
  by_cases hxi : x = i
  · subst x; simp [swapSet,Finset.mem_map_equiv,hi,hj]
  by_cases hxj : x = j
  · subst x; simp [swapSet,Finset.mem_map_equiv,hi,hj]
  simp [swapSet,Finset.mem_map_equiv,Equiv.swap_apply_of_ne_of_ne hxi hxj]

theorem swapSet_move (i j : ℕ) (hij : i ≠ j) (A : Finset ℕ) (hi : i ∉ A) (hj : j ∈ A) :
    swapSet i j A = (A ∪ {i}) \ {j} := by
  ext x
  by_cases hxi : x = i
  · subst x; simp [swapSet,Finset.mem_map_equiv,hi,hj,hij]
  by_cases hxj : x = j
  · subst x; simp [swapSet,Finset.mem_map_equiv,hi,hj,hij]
  simp [swapSet,Finset.mem_map_equiv,Equiv.swap_apply_of_ne_of_ne hxi hxj,hxi,hxj]

theorem swapSet_reverse (i j : ℕ) (hij : i ≠ j) (A : Finset ℕ) (hi : i ∈ A) (hj : j ∉ A) :
    swapSet i j A = (A ∪ {j}) \ {i} := by
  rw [show swapSet i j A = swapSet j i A by simp [swapSet,Equiv.swap_comm]]
  exact swapSet_move j i hij.symm A hj hi

def shift (i j : ℕ) (F : Finset (Finset ℕ)) := UV.compression ({i}:Finset ℕ) {j} F

theorem shift_card (i j : ℕ) (F : Finset (Finset ℕ)) : (shift i j F).card = F.card :=
  UV.card_compression _ _ _

theorem new_contains (i j : ℕ) (F : Finset (Finset ℕ)) (A : Finset ℕ)
    (hA : A ∈ shift i j F) (hnot : A ∉ F) : i ∈ A := by
  simpa using UV.le_of_mem_compression_of_notMem hA hnot

theorem new_excludes (i j : ℕ) (F : Finset (Finset ℕ)) (A : Finset ℕ)
    (hA : A ∈ shift i j F) (hnot : A ∉ F) : j ∉ A := by
  simpa using UV.disjoint_of_mem_compression_of_notMem hA hnot

theorem swap_new_mem (i j : ℕ) (hij : i ≠ j) (F : Finset (Finset ℕ)) (A : Finset ℕ)
    (hA : A ∈ shift i j F) (hnot : A ∉ F) : swapSet i j A ∈ F := by
  rw [swapSet_reverse i j hij A (new_contains i j F A hA hnot) (new_excludes i j F A hA hnot)]
  exact UV.sup_sdiff_mem_of_mem_compression_of_notMem hA hnot

theorem swap_absent_mem (i j : ℕ) (hij : i ≠ j) (F : Finset (Finset ℕ)) (A : Finset ℕ)
    (hA : A ∈ shift i j F) (hi : i ∉ A) : swapSet i j A ∈ F := by
  by_cases hj : j ∈ A
  · rw [swapSet_move i j hij A hi hj]
    exact UV.sup_sdiff_mem_of_mem_compression hA (by simpa) (by simpa)
  · rw [swapSet_absent i j A hi hj]
    by_contra hn
    exact hi (new_contains i j F A hA hn)
end FranklKupavskii2022.EMC.Shifting

namespace FranklKupavskii2022.EMC.Shifting
open Finset

def IsMatching (M : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B

theorem matching_card_le (F M : Finset (Finset ℕ)) (hMF : M ⊆ F) (hM : IsMatching M) :
    M.card ≤ matchingNumber F := by
  apply Finset.le_sup (f := Finset.card)
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hMF,hM⟩

theorem matchingNumber_le (F : Finset (Finset ℕ)) (b : ℕ)
    (h : ∀ M ⊆ F, IsMatching M → M.card ≤ b) : matchingNumber F ≤ b := by
  unfold matchingNumber
  apply Finset.sup_le
  intro M hM
  rw [Finset.mem_filter,Finset.mem_powerset] at hM
  exact h M hM.1 hM.2

theorem matching_swap (i j : ℕ) (M : Finset (Finset ℕ)) (hM : IsMatching M) :
    IsMatching (M.image (swapSet i j)) := by
  intro A hA B hB hne
  obtain ⟨A',hA',rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨B',hB',rfl⟩ := Finset.mem_image.mp hB
  apply (swapSet_disjoint i j A' B').mpr
  exact hM A' hA' B' hB' (fun he => hne (congrArg (swapSet i j) he))

theorem matching_lift (i j : ℕ) (hij : i ≠ j) (F M : Finset (Finset ℕ))
    (hMF : M ⊆ shift i j F) (hM : IsMatching M) :
    ∃ N ⊆ F, IsMatching N ∧ N.card = M.card := by
  classical
  by_cases hs : M ⊆ F
  · exact ⟨M,hs,hM,rfl⟩
  obtain ⟨A,hAM,hAF⟩ := Finset.not_subset.mp hs
  have hiA := new_contains i j F A (hMF hAM) hAF
  refine ⟨M.image (swapSet i j), ?_, matching_swap i j M hM, ?_⟩
  · intro B hB
    obtain ⟨C,hCM,rfl⟩ := Finset.mem_image.mp hB
    by_cases he : C = A
    · subst C
      exact swap_new_mem i j hij F A (hMF hAM) hAF
    · apply swap_absent_mem i j hij F C (hMF hCM)
      exact Finset.disjoint_left.mp (hM A hAM C hCM (Ne.symm he)) hiA
  · exact Finset.card_image_of_injective _ (swapSet_injective i j)

theorem matchingNumber_shift_le (i j : ℕ) (F : Finset (Finset ℕ)) :
    matchingNumber (shift i j F) ≤ matchingNumber F := by
  by_cases hij : i = j
  · subst j
    simp [shift]
  apply matchingNumber_le
  intro M hMF hM
  obtain ⟨N,hNF,hN,hcard⟩ := matching_lift i j hij F M hMF hM
  rw [← hcard]
  exact matching_card_le F N hNF hN

theorem compress_subset (i j : ℕ) (A U : Finset ℕ) (hA : A ⊆ U) (hi : i ∈ U) :
    UV.compress ({i}:Finset ℕ) {j} A ⊆ U := by
  unfold UV.compress
  split_ifs
  · exact Finset.Subset.trans Finset.sdiff_subset (Finset.union_subset hA (by simpa))
  · exact hA

theorem shift_uniform (m k i j : ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Finset.Icc 1 m).powersetCard k) (hi : i ∈ Finset.Icc 1 m) :
    shift i j F ⊆ (Finset.Icc 1 m).powersetCard k := by
  intro A hA
  obtain h | ⟨_,B,hB,rfl⟩ := UV.mem_compression.mp hA
  · exact hF h.1
  obtain ⟨hBU,hBk⟩ := Finset.mem_powersetCard.mp (hF hB)
  apply Finset.mem_powersetCard.mpr
  exact ⟨compress_subset i j B _ hBU hi,(UV.card_compress (by simp) B).trans hBk⟩
end FranklKupavskii2022.EMC.Shifting

namespace FranklKupavskii2022.EMC.Shifting
open Finset

def weight (A : Finset ℕ) : ℕ := ∑ x ∈ A,x

def mass (F : Finset (Finset ℕ)) : ℕ := ∑ A ∈ F,weight A

theorem compress_weight_lt (i j : ℕ) (hij : i < j) (A : Finset ℕ)
    (hne : UV.compress ({i}:Finset ℕ) {j} A ≠ A) :
    weight (UV.compress ({i}:Finset ℕ) {j} A) < weight A := by
  have hc : i ∉ A ∧ j ∈ A := by
    by_contra h
    apply hne
    simp [UV.compress,h]
  have he : UV.compress ({i}:Finset ℕ) {j} A = insert i (A.erase j) := by
    rw [UV.compress_of_disjoint_of_le (by simpa using hc.1) (by simpa using hc.2)]
    ext x
    simp only [sup_eq_union,mem_sdiff,mem_union,mem_singleton,mem_insert,mem_erase]
    grind
  rw [he,weight,Finset.sum_insert (by simp [hc.1])]
  have hs := Finset.sum_erase_add A (fun x : ℕ => x) hc.2
  dsimp [weight]
  omega

-- The filter partition and sum argument follows Mathlib's UV family-measure
-- descent proof in KruskalKatona.lean (Yaël Dillies and Bhavik Mehta, Apache-2.0).
-- Here the potential is the sum of labels and only singleton shifts are used.
theorem mass_shift_lt (i j : ℕ) (hij : i < j) (F : Finset (Finset ℕ))
    (hne : shift i j F ≠ F) : mass (shift i j F) < mass F := by
  classical
  let u : Finset ℕ := {i}
  let v : Finset ℕ := {j}
  have q : ∀ A ∈ {A ∈ F | UV.compress u v A ∉ F}, UV.compress u v A ≠ A := by
    intro A hA he
    have hh := Finset.mem_filter.mp hA
    exact hh.2 (by rw [he]; exact hh.1)
  have hpart : {A ∈ F | UV.compress u v A ∈ F} ∪ {A ∈ F | UV.compress u v A ∉ F} = F :=
    Finset.filter_union_filter_not_eq _ _
  have hne' : ({A ∈ F | UV.compress u v A ∉ F}).Nonempty := by
    by_contra hn
    have he : {A ∈ F | UV.compress u v A ∉ F} = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hne
    change UV.compression u v F = F
    rw [UV.compression,Finset.filter_image,he,Finset.image_empty,Finset.union_empty]
    rwa [he,Finset.union_empty] at hpart
  change mass (UV.compression u v F) < mass F
  rw [UV.compression,mass,mass,Finset.sum_union UV.compress_disjoint]
  conv_rhs => rw [← hpart]
  rw [Finset.sum_union (Finset.disjoint_filter_filter_not _ _ _),add_lt_add_iff_left,
    Finset.filter_image,Finset.sum_image UV.compress_injOn]
  exact Finset.sum_lt_sum_of_nonempty hne' (fun A hA => compress_weight_lt i j hij A (q A hA))

def Stable (m : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m, i < j → shift i j F = F

theorem stable_family_exists (m k : ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Finset.Icc 1 m).powersetCard k) :
    ∃ G, G ⊆ (Finset.Icc 1 m).powersetCard k ∧ Stable m G ∧
      G.card = F.card ∧ matchingNumber G ≤ matchingNumber F := by
  classical
  by_cases hS : Stable m F
  · exact ⟨F,hF,hS,rfl,le_rfl⟩
  unfold Stable at hS
  push Not at hS
  obtain ⟨i,hi,j,hj,hij,hne⟩ := hS
  obtain ⟨G,hG,hGS,hcard,hmatch⟩ := stable_family_exists m k (shift i j F) (shift_uniform m k i j F hF hi)
  exact ⟨G,hG,hGS,hcard.trans (shift_card i j F),hmatch.trans (matchingNumber_shift_le i j F)⟩
termination_by mass F
decreasing_by exact mass_shift_lt i j hij F hne
end FranklKupavskii2022.EMC.Shifting

namespace FranklKupavskii2022.EMC.Shifting
open Finset

def LowerClosed (U : Set ℕ) (P : Finset ℕ → Prop) : Prop :=
  ∀ A, (∀ x ∈ A, x ∈ U) → P A → ∀ i ∈ U, ∀ j ∈ A,
    i ∉ A → i < j → P (insert i (A.erase j))

theorem lowerClosed_insert (U : Set ℕ) (P : Finset ℕ → Prop)
    (hP : LowerClosed U P) (a : ℕ) (ha : a ∈ U) :
    LowerClosed {x | x ∈ U ∧ a < x} (fun A => P (insert a A)) := by
  intro A hA hp i hi j hj hni hij
  have hja : j ≠ a := (ne_of_gt (hA j hj).2)
  have hia : i ≠ a := ne_of_gt hi.2
  have hU : ∀ x ∈ insert a A, x ∈ U := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ha
    · exact (hA x hx).1
  have h := hP (insert a A) hU hp i hi.1 j (mem_insert_of_mem hj)
    (by simp [hia,hni]) hij
  simpa [erase_insert_of_ne hja.symm, insert_comm] using h

theorem lowerClosed_of_forall₂ (U : Set ℕ) (P : Finset ℕ → Prop)
    (hP : LowerClosed U P) (as bs : List ℕ)
    (hAB : List.Forall₂ (· ≤ ·) as bs)
    (hA : as.Pairwise (· < ·)) (hB : bs.Pairwise (· < ·))
    (hAU : ∀ x ∈ as, x ∈ U) (hBU : ∀ x ∈ bs, x ∈ U)
    (hp : P bs.toFinset) : P as.toFinset := by
  classical
  induction hAB generalizing U P with
  | nil => exact hp
  | @cons a b as bs hab hrel ih =>
    obtain ⟨ha,haTail⟩ := List.pairwise_cons.mp hA
    obtain ⟨hb,hbTail⟩ := List.pairwise_cons.mp hB
    have haU : a ∈ U := hAU a (by simp)
    have hba : ∀ x ∈ bs, a < x := fun x hx => lt_of_le_of_lt hab (hb x hx)
    have hbnot : b ∉ bs.toFinset := by
      simp only [List.mem_toFinset]
      exact fun h => (lt_irrefl b) (hb b h)
    have hp' : P (insert a bs.toFinset) := by
      by_cases he : a = b
      · subst b
        simpa using hp
      · have hna : a ∉ (b :: bs).toFinset := by
          simp only [List.toFinset_cons, mem_insert, List.mem_toFinset, not_or]
          exact ⟨he,fun h => (lt_irrefl a) (hba a h)⟩
        have h := hP (b :: bs).toFinset
          (fun x hx => hBU x (List.mem_toFinset.mp hx)) hp a haU b (by simp)
          hna (lt_of_le_of_ne hab he)
        simpa [hbnot] using h
    have hsmall : LowerClosed {x | x ∈ U ∧ a < x} (fun A => P (insert a A)) :=
      lowerClosed_insert U P hP a haU
    have hAU' : ∀ x ∈ as, x ∈ ({x | x ∈ U ∧ a < x} : Set ℕ) := by
      intro x hx
      exact ⟨hAU x (by simp [hx]),ha x hx⟩
    have hBU' : ∀ x ∈ bs, x ∈ ({x | x ∈ U ∧ a < x} : Set ℕ) := by
      intro x hx
      exact ⟨hBU x (by simp [hx]),hba x hx⟩
    simpa using ih {x | x ∈ U ∧ a < x} (fun A => P (insert a A))
      hsmall haTail hbTail hAU' hBU' hp'

theorem stable_lowerClosed (m : ℕ) (F : Finset (Finset ℕ)) (hS : Stable m F) :
    LowerClosed (↑(Icc 1 m)) (fun A => A ∈ F) := by
  intro A hA hAF i hi j hj hni hij
  have hc := UV.compress_mem_compression (u := ({i}:Finset ℕ)) (v := {j}) hAF
  change UV.compress ({i}:Finset ℕ) {j} A ∈ shift i j F at hc
  rw [hS i hi j (hA j hj) hij] at hc
  have he : UV.compress ({i}:Finset ℕ) {j} A = insert i (A.erase j) := by
    rw [UV.compress_of_disjoint_of_le (by simpa using hni) (by simpa using hj)]
    ext x
    simp only [sup_eq_union,mem_sdiff,mem_union,mem_singleton,mem_insert,mem_erase]
    grind
  rwa [← he]

theorem stable_initial (m k : ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Icc 1 m).powersetCard k) (hS : Stable m F) : IsInitial m k F := by
  intro A hA B hB hAB
  have hAU := (mem_powersetCard.mp hA).1
  have hBU := (mem_powersetCard.mp (hF hB)).1
  have h := lowerClosed_of_forall₂ (↑(Icc 1 m)) (fun A => A ∈ F)
    (stable_lowerClosed m F hS) A.sort B.sort hAB.1
    A.sortedLT_sort.pairwise B.sortedLT_sort.pairwise
    (fun x hx => hAU (by simpa using hx)) (fun x hx => hBU (by simpa using hx))
    (by simpa using hB)
  simpa using h

end FranklKupavskii2022.EMC.Shifting

open FranklKupavskii2022.EMC FranklKupavskii2022.EMC.Shifting

theorem solution (m k : ℕ) (Ft : Finset (Finset ℕ))
    (hFt : Ft ⊆ (Finset.Icc 1 m).powersetCard k) :
    ∃ F : Finset (Finset ℕ), F ⊆ (Finset.Icc 1 m).powersetCard k ∧ IsInitial m k F ∧
      F.card = Ft.card ∧ matchingNumber F ≤ matchingNumber Ft := by
  obtain ⟨F,hF,hS,hcard,hmatch⟩ := stable_family_exists m k Ft hFt
  exact ⟨F,hF,stable_initial m k F hF hS,hcard,hmatch⟩
