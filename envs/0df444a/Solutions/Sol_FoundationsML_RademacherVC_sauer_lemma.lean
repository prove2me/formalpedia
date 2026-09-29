-- Prove2me | solution 1 for FoundationsML.RademacherVC.sauer_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:16:38.84757+00:00
-- url     : https://prove2.me/submissions/ba81fbb7-59de-4724-ad86-ef49d1b9dc99

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim

namespace FoundationsML.RademacherVC

theorem aux_sl_card_le_pow {X : Type*} (H : Set (X → Bool)) (k : ℕ) (x : Fin k → X) :
    Nat.card {t : Fin k → Bool // ∃ h ∈ H, t = h ∘ x} ≤ 2 ^ k := by
  calc Nat.card {t : Fin k → Bool // ∃ h ∈ H, t = h ∘ x} ≤ Nat.card (Fin k → Bool) :=
        Finite.card_subtype_le _
    _ = 2 ^ k := by simp

theorem aux_sl_growth_le {X : Type*} (H : Set (X → Bool)) (k : ℕ) :
    GrowthFunction H k ≤ 2 ^ k := by
  unfold GrowthFunction
  exact ciSup_le' (fun x => aux_sl_card_le_pow H k x)

theorem aux_sl_full {X : Type*} (H : Set (X → Bool)) (k : ℕ) (y : Fin k → X)
    (hy : ∀ t : Fin k → Bool, ∃ h ∈ H, t = h ∘ y) : GrowthFunction H k = 2 ^ k := by
  apply le_antisymm (aux_sl_growth_le H k)
  have hc : Nat.card {t : Fin k → Bool // ∃ h ∈ H, t = h ∘ y} = 2 ^ k := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hy)]
    simp
  have hb : BddAbove (Set.range fun x : Fin k → X =>
      Nat.card {t : Fin k → Bool // ∃ h ∈ H, t = h ∘ x}) := by
    refine ⟨2 ^ k, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact aux_sl_card_le_pow H k x
  rw [← hc]
  unfold GrowthFunction
  exact le_ciSup hb y

theorem aux_sl_card {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (m : ℕ)
    (x : Fin m → X) :
    Nat.card {t : Fin m → Bool // ∃ h ∈ H, t = h ∘ x} ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  classical
  open Finset in
  set T : Finset (Fin m → Bool) := univ.filter (fun t => ∃ h ∈ H, t = h ∘ x) with hT
  let f : (Fin m → Bool) → Finset (Fin m) := fun t => Finset.univ.filter (fun i => t i = true)
  have hf : Function.Injective f := by
    intro t₁ t₂ h
    funext i
    have := congrArg (i ∈ ·) h
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases h1 : t₁ i <;> cases h2 : t₂ i <;> simp_all
  set 𝒜 := T.image f with h𝒜
  have hcard : Nat.card {t : Fin m → Bool // ∃ h ∈ H, t = h ∘ x} = 𝒜.card := by
    rw [Finset.card_image_of_injective _ hf, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hvc : ∀ s ∈ 𝒜.shatterer, s.card ≤ d := by
    intro s hs
    rw [Finset.mem_shatterer] at hs
    apply hH.2
    let e := s.orderEmbOfFin rfl
    apply aux_sl_full H _ (x ∘ e)
    intro t
    obtain ⟨A, hA, hsA⟩ := hs (t := (Finset.univ.filter (fun j => t j = true)).map e.toEmbedding)
      (by
        intro i hi
        simp only [Finset.mem_map] at hi
        obtain ⟨j, _, rfl⟩ := hi
        exact s.orderEmbOfFin_mem rfl j)
    rw [h𝒜, Finset.mem_image] at hA
    obtain ⟨t', ht', rfl⟩ := hA
    rw [hT, Finset.mem_filter] at ht'
    obtain ⟨h, hH', rfl⟩ := ht'.2
    refine ⟨h, hH', ?_⟩
    funext j
    have key := congrArg (e j ∈ ·) hsA
    simp only [f, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, eq_iff_iff] at key
    have hej : e j ∈ s := s.orderEmbOfFin_mem rfl j
    have key2 : (h ∘ x) (e j) = true ↔ t j = true := by
      constructor
      · intro hh
        obtain ⟨a, ha, hae⟩ := key.1 ⟨hej, hh⟩
        have : a = j := e.toEmbedding.injective hae
        subst this
        exact ha
      · intro ht
        exact (key.2 ⟨j, ht, rfl⟩).2
    simp only [Function.comp_apply] at key2 ⊢
    cases h1 : t j <;> cases h2 : h (x (e j)) <;> simp_all
  rw [hcard]
  calc 𝒜.card ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card (Fin m)).choose k :=
        Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card (Fin m)).choose k := by
        apply Finset.sum_le_sum_of_subset
        apply Finset.Iic_subset_Iic.2
        exact Finset.sup_le hvc
    _ = ∑ i ∈ Finset.range (d + 1), m.choose i := by
        rw [Fintype.card_fin]
        congr 1
        ext i
        simp

end FoundationsML.RademacherVC

open FoundationsML.RademacherVC

theorem solution
    {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (m : ℕ) :
    GrowthFunction H m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  unfold GrowthFunction
  exact ciSup_le' (fun x => aux_sl_card H d hH m x)
