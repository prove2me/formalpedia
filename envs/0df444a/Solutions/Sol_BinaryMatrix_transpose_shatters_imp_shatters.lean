-- Prove2me | solution 1 for BinaryMatrix.transpose_shatters_imp_shatters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:45.653827+00:00
-- url     : https://prove2.me/submissions/d771c045-c9e5-4e40-8549-ba7ffc7b1955

module
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_BinaryMatrix

set_option autoImplicit true
@[expose] public section
public section
open Finset
universe u
open BinaryMatrix
namespace BinaryMatrix
theorem _root_.solution {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (S : Finset (Fin m)) (hS : M.transpose.shatters S)
    (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset (Fin n), T.card = d + 1 ∧ M.shatters T := by
  -- Embed (Fin (d+1) → Bool) into S
  let eS := S.equivFin
  let eFun : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq (by simp)
  let eFin : Fin (2 ^ (d + 1)) ↪ Fin S.card := Fin.castLEEmb hcard
  let eFinS : Fin S.card ≃ ↥S := eS.symm
  let embed : (Fin (d + 1) → Bool) → ↥S := eFinS ∘ eFin ∘ eFun
  have hembed_inj : Function.Injective embed := by
    intro a b hab
    simp only [embed, Function.comp] at hab
    exact eFun.injective (eFin.injective (eFinS.injective hab))
  -- For each coordinate k, define the "k-th half" subset T_k ⊆ S
  -- T_k = {embed(b) | b(k) = true} viewed as a subset of S
  let T_k (k : Fin (d + 1)) : Finset (Fin m) :=
    S.filter (fun i => ∃ b : Fin (d + 1) → Bool, (embed b).val = i ∧ b k = true)
  have hT_k_sub : ∀ k, T_k k ⊆ S := fun k => Finset.filter_subset _ _
  -- M^T shattering gives columns c_k witnessing T_k
  have hcols : ∀ k : Fin (d + 1), ∃ c : Fin n, ∀ i ∈ S,
      (M i c = true ↔ i ∈ T_k k) := by
    intro k
    obtain ⟨c, hc⟩ := hS (T_k k) (hT_k_sub k)
    exact ⟨c, fun i hi => by simpa only [transpose] using hc i hi⟩
  choose c hc using hcols
  -- The key property: M (embed b) (c k) = b k
  have hM_embed : ∀ (b : Fin (d + 1) → Bool) (k : Fin (d + 1)),
      M (embed b).val (c k) = b k := by
    intro b k
    have hemb_mem : (embed b).val ∈ S := (embed b).property
    by_cases hbk : b k = true
    · -- b k = true, so embed b ∈ T_k k
      have hmem : (embed b).val ∈ T_k k := by
        simp only [T_k, Finset.mem_filter]
        exact ⟨hemb_mem, ⟨b, rfl, hbk⟩⟩
      rw [(hc k _ hemb_mem).mpr hmem, hbk]
    · -- b k = false, so embed b ∉ T_k k
      simp only [Bool.not_eq_true] at hbk
      have hmem : (embed b).val ∉ T_k k := by
        simp only [T_k, Finset.mem_filter, not_and]
        intro _
        rintro ⟨b', hb'eq, hb'k⟩
        have : embed b' = embed b := by
          exact Subtype.val_injective (by rw [hb'eq])
        have := hembed_inj this
        simp_all
      rw [Bool.eq_false_iff.mpr (mt (hc k _ hemb_mem).mp hmem), hbk]
  -- Build T = {c 0, c 1, ..., c d}
  let T : Finset (Fin n) := Finset.univ.image c
  -- The c_k are distinct
  have hc_inj : Function.Injective c := by
    intro j k hjk
    by_contra hjk_ne
    -- Choose b with b j = true, b k = false
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    have h1 : M (embed b0).val (c j) = true := by
      rw [hM_embed b0 j]; simp [b0]
    have h2 : M (embed b0).val (c k) = false := by
      rw [hM_embed b0 k]; simp only [b0]
      cases hkj : (k == j)
      · rfl
      · exact absurd (beq_iff_eq.mp hkj).symm hjk_ne
    simp_all
  have hT_card : T.card = d + 1 := by
    simp only [T, card_image_of_injective _ hc_inj, card_univ, Fintype.card_fin]
  -- M shatters T
  have hT_shatters : M.shatters T := by
    intro t ht
    -- t ⊆ T. Define g : Fin (d+1) → Bool by g(k) = (c k ∈ t)
    let g : Fin (d + 1) → Bool := fun k => decide (c k ∈ t)
    -- The row embed(g) witnesses t
    refine ⟨(embed g).val, fun j hj => ?_⟩
    -- j ∈ T means j = c k for some k
    simp only [T] at hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, _, rfl⟩ := hj
    rw [hM_embed g k]
    simp only [g, decide_eq_true_eq]
  exact ⟨T, hT_card, hT_shatters⟩
end BinaryMatrix
