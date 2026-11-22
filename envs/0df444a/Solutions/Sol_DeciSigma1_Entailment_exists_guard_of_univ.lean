-- Prove2me | solution 1 for DeciSigma1.Entailment.exists_guard_of_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:21:06.652797+00:00
-- url     : https://prove2.me/submissions/6439b3b6-7497-4d7d-847d-48a8ea6f1275

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_le_univ


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment
open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n k : ℕ} {V : Type}
namespace DeciSigma1.Entailment
theorem _root_.solution {C : PrefixSet n → Prop} (hC : C PrefixSet.univ)
    (ρ : V → PrefixSet n) : ∃ g, C g ∧ g ≤ PrefixSet.node (fun _ => g) ∧ ∀ v, ρ v ≤ g :=
  ⟨PrefixSet.univ, hC, PrefixSet.node_univ.ge, fun v => PrefixSet.le_univ (ρ v)⟩
end DeciSigma1.Entailment
