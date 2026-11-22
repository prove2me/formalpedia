-- Prove2me | solution 1 for DeciSigma1.Entailment.disjEntailsIn_finite_iff_guarded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:29:01.092116+00:00
-- url     : https://prove2.me/submissions/b450c78c-b29e-4427-9881-3f0e6f1d9ac1

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
public import Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_iff_guarded_of_classes
public import Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_complete
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_complete_le_node
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_finiteTop_toTree_iff
public import Theorems.Thm_DeciSigma1_Semantics_exists_le_complete
public import Theorems.Thm_DeciSigma1_Semantics_isFiniteTree_complete


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment
open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n k : ℕ} {V : Type}
namespace DeciSigma1.Entailment
theorem _root_.solution {vs : List V} (hvs : ∀ v, v ∈ vs)
    (Γ : List (Lit n V)) (q : Fin k → V × V) :
    DisjEntailsIn IsFiniteTree Γ q ↔
      Full.DisjEntailsIn Full.Models.FiniteTop (fun _ => false) (guarded vs Γ)
        (guardedQueries q) := by
  classical
  have : Finite V := Set.finite_univ_iff.mp (vs.finite_toSet.subset fun v _ => hvs v)
  refine disjEntailsIn_iff_guarded_of_classes PrefixSet.finiteTop_toTree_iff
    (fun ρ hρ => ?_) hvs Γ q
  obtain ⟨d, hd⟩ := exists_le_complete hρ
  exact ⟨PrefixSet.complete d, isFiniteTree_complete d, PrefixSet.complete_le_node d, hd⟩
end DeciSigma1.Entailment
