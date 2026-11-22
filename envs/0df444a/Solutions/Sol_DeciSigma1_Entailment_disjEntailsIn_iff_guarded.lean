-- Prove2me | solution 1 for DeciSigma1.Entailment.disjEntailsIn_iff_guarded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:37.189727+00:00
-- url     : https://prove2.me/submissions/1bd65a6b-b814-42d8-a390-846564f44095

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
public import Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_iff_guarded_of_classes
public import Theorems.Thm_DeciSigma1_Entailment_exists_guard_of_univ

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment
open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n k : ℕ} {V : Type}
namespace DeciSigma1.Entailment
theorem _root_.solution {vs : List V} (hvs : ∀ v, v ∈ vs) (Γ : List (Lit n V))
    (q : Fin k → V × V) :
    DisjEntailsIn (fun _ => True) Γ q ↔
      Full.DisjEntailsIn (fun _ => True) (fun _ => false) (guarded vs Γ) (guardedQueries q) :=
  disjEntailsIn_iff_guarded_of_classes (D := fun _ => True) (fun _ => Iff.rfl)
    (fun ρ _ => exists_guard_of_univ trivial ρ) hvs Γ q
end DeciSigma1.Entailment
