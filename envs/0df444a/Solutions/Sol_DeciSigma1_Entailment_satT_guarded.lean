-- Prove2me | solution 1 for DeciSigma1.Entailment.satT_guarded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:24:22.903351+00:00
-- url     : https://prove2.me/submissions/02e77e60-f2d0-4b4e-bcab-3b03947b9051

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
attribute [local simp] DeciSigma1.Constraints.holdsT_map
attribute [local simp] DeciSigma1.Semantics.treeLe_false_iff_le



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment
open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n k : ℕ} {V : Type}
namespace DeciSigma1.Entailment
theorem _root_.solution (vs : List V) (Γ : List (Lit n V)) (σ : Option V → Semantics.Tree n) :
    SatT (fun _ => false) σ (guarded vs Γ) ↔
      σ none ≤ Semantics.Tree.node (fun _ => σ none) ∧ (∀ v ∈ vs, σ (some v) ≤ σ none) ∧
        ∀ l ∈ Γ, HoldsT (fun _ => false) (σ ∘ some) l.toLitT := by
  constructor
  · intro h
    exact ⟨(treeLe_false_iff_le _ _).mp (h _ List.mem_cons_self),
      fun v hv => (treeLe_false_iff_le _ _).mp (h (.le (some v) none)
        (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hv)))),
      fun l hl => (holdsT_map _ _ _ _).mp
        (h _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem hl))))⟩
  · rintro ⟨hu, hle, hΓ⟩ l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact (treeLe_false_iff_le _ _).mpr hu
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
      exact (treeLe_false_iff_le _ _).mpr (hle v hv)
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      exact (holdsT_map _ _ _ _).mpr (hΓ l' hl')
end DeciSigma1.Entailment
