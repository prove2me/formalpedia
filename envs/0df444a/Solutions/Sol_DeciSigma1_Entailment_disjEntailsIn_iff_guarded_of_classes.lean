-- Prove2me | solution 1 for DeciSigma1.Entailment.disjEntailsIn_iff_guarded_of_classes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:53.81459+00:00
-- url     : https://prove2.me/submissions/1d9c65a0-2cb2-46e1-9e6f-4740f0fa26f4

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
public import Theorems.Thm_DeciSigma1_Constraints_TopFree_holdsT_toLitT
public import Theorems.Thm_DeciSigma1_Entailment_satT_guarded
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_le_toTree
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_isTopFree_of_le_of_le_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_toTree_positions
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.PrefixSet.toTree_le_toTree
attribute [local simp] DeciSigma1.Semantics.treeLe_false_iff_le



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment
open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n k : ℕ} {V : Type}
namespace DeciSigma1.Entailment
theorem _root_.solution {C : PrefixSet n → Prop}
    {D : Semantics.Tree n → Prop} (hD : ∀ P, D P.toTree ↔ C P)
    (hC : ∀ ρ : V → PrefixSet n, (∀ v, C (ρ v)) →
      ∃ g, C g ∧ g ≤ PrefixSet.node (fun _ => g) ∧ ∀ v, ρ v ≤ g)
    {vs : List V} (hvs : ∀ v, v ∈ vs) (Γ : List (Lit n V)) (q : Fin k → V × V) :
    DisjEntailsIn C Γ q ↔
      Full.DisjEntailsIn D (fun _ => false) (guarded vs Γ) (guardedQueries q) := by
  constructor
  · intro h σ hσ hsat
    obtain ⟨hu, hle, hΓ⟩ := (satT_guarded vs Γ σ).mp hsat
    have ht (v : V) : (σ (some v)).positions.toTree = σ (some v) :=
      Tree.toTree_positions (Tree.isTopFree_of_le_of_le_node hu (hle v (hvs v)))
    have he : (fun v => (σ (some v)).positions.toTree) = σ ∘ some := funext ht
    obtain ⟨i, hi⟩ := h (fun v => (σ (some v)).positions)
      (fun v => (hD _).mp (by rw [ht]; exact hσ (some v)))
      (fun l hl => (holdsT_toLitT _ l).mp (by rw [he]; exact hΓ l hl))
    refine ⟨i, (treeLe_false_iff_le _ _).mpr ?_⟩
    change σ (some (q i).1) ≤ σ (some (q i).2)
    rw [← ht (q i).1, ← ht (q i).2]
    exact (PrefixSet.toTree_le_toTree _ _).mpr hi
  · intro h ρ hρ hsat
    obtain ⟨g, hg, hgg, hρg⟩ := hC ρ hρ
    let σ : Option V → Semantics.Tree n := fun o => (o.elim g ρ).toTree
    obtain ⟨i, hi⟩ := h σ
      (fun o => (hD _).mpr (by cases o; exacts [hg, hρ _]))
      ((satT_guarded vs Γ σ).mpr
        ⟨(PrefixSet.toTree_node _).symm ▸ (PrefixSet.toTree_le_toTree _ _).mpr hgg,
          fun v _ => (PrefixSet.toTree_le_toTree _ _).mpr (hρg v),
          fun l hl => (holdsT_toLitT ρ l).mpr (hsat l hl)⟩)
    exact ⟨i, (PrefixSet.toTree_le_toTree _ _).mp ((treeLe_false_iff_le _ _).mp hi)⟩
end DeciSigma1.Entailment
