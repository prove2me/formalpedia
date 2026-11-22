-- Prove2me | solution 1 for DualVC.dual_shatters_imp_original_shatters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:21.766284+00:00
-- url     : https://prove2.me/submissions/ad0e0ab0-b5d1-4471-90ae-7b90e3abf7a9

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_DualVC

set_option autoImplicit true
@[expose] public section
public section
open Finset
universe u
open DualVC
variable {X : Type u} {C : ConceptClass X Bool}
namespace DualVC
theorem _root_.solution {d : ℕ}
    (S : Finset ↥C) (hS : Shatters ↥C (DualClass X C) S)
    (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset X, T.card = d + 1 ∧ Shatters X C T := by
  classical
  -- Embed the `2^(d+1)` bitstrings into `↥S` as a subset of the shattered concepts.
  let eS := S.equivFin
  have h2le : 2 ^ (d + 1) ≤ S.card := hcard
  let eFun : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_bool, Fintype.card_fin])
  let eFin : Fin (2 ^ (d + 1)) ↪ Fin S.card := Fin.castLEEmb h2le
  let eFinS : Fin S.card ≃ ↥S := eS.symm
  let embed : (Fin (d + 1) → Bool) → ↥S := eFinS ∘ eFin ∘ eFun
  have hembed_inj : Function.Injective embed := by
    intro a b hab
    simp only [embed, Function.comp] at hab
    exact eFun.injective (eFin.injective (eFinS.injective hab))
  -- For coordinate `j`, label each embedded concept by its `j`-th bit (and `false` elsewhere).
  let label (j : Fin (d + 1)) : ↥S → Bool := fun s =>
    if h : ∃ b, embed b = s then (h.choose) j else false
  -- Dual shattering of each labeling yields a point `x j` reading off the `j`-th bit.
  have hpoints : ∀ j : Fin (d + 1), ∃ x : X, ∀ s : ↥S,
      (s : ↥C).val x = label j s := by
    intro j
    obtain ⟨f, ⟨x, hx⟩, hf_eq⟩ := hS (label j)
    exact ⟨x, fun s => by rw [← hx s, ← hf_eq s]⟩
  choose x hx using hpoints
  let T : Finset X := Finset.univ.image x
  -- The `x j` are distinct: a bitstring singleton at `j` separates coordinates `j ≠ k`.
  have hx_inj : Function.Injective x := by
    intro j k hjk
    by_contra hjk_ne
    have hlabel_eq : ∀ s : ↥S, label j s = label k s := by
      intro s
      have hj := hx j s
      simp_all
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    have hlabel_j_b0 : label j (embed b0) = true := by
      simp only [label]
      rw [dif_pos ⟨b0, rfl⟩,
        hembed_inj (⟨b0, rfl⟩ : ∃ b, embed b = embed b0).choose_spec]
      simp [b0]
    have hlabel_k_b0 : label k (embed b0) = false := by
      simp only [label]
      rw [dif_pos ⟨b0, rfl⟩,
        hembed_inj (⟨b0, rfl⟩ : ∃ b, embed b = embed b0).choose_spec]
      simp only [b0]
      cases hkj : (k == j)
      · rfl
      · exact absurd (beq_iff_eq.mp hkj).symm hjk_ne
    simp_all
  have hT_card : T.card = d + 1 := by
    simp only [T, card_image_of_injective _ hx_inj, card_univ, Fintype.card_fin]
  -- `C` shatters `T`: realise labeling `f` by the concept `embed g`, where `g j = f (x j)`.
  have hT_shatters : Shatters X C T := by
    intro f
    have hx_mem : ∀ j : Fin (d + 1), x j ∈ T := by
      intro j; simp only [T]; exact mem_image_of_mem _ (mem_univ _)
    let g : Fin (d + 1) → Bool := fun j => f ⟨x j, hx_mem j⟩
    let cg : ↥C := (embed g).val
    refine ⟨cg.val, cg.property, fun ⟨y, hy⟩ => ?_⟩
    simp only [T] at hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, _, rfl⟩ := hy
    change cg.val (x j) = f ⟨x j, hx_mem j⟩
    have step1 : (embed g).val.val (x j) = label j (embed g) := hx j (embed g)
    have step2 : label j (embed g) = g j := by
      simp only [label]
      rw [dif_pos ⟨g, rfl⟩,
        hembed_inj (⟨g, rfl⟩ : ∃ b, embed b = embed g).choose_spec]
    rw [step1, step2]
  exact ⟨T, hT_card, hT_shatters⟩
end DualVC
