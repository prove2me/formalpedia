-- Prove2me | solution 1 for DeciSigma1.Entailment.disjEntailsIn_regular_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:09.326466+00:00
-- url     : https://prove2.me/submissions/29194722-ba45-4c28-a09f-ad6d14021856

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
public import Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_iff_guarded
public import Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_regular_iff_guarded
public import Theorems.Thm_DeciSigma1_Full_Reduction_disjEntails_regular_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment
open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n k : ℕ} {V : Type}
namespace DeciSigma1.Entailment
theorem _root_.solution [Finite V] (Γ : List (Lit n V))
    (q : Fin k → V × V) :
    DisjEntailsIn IsRegularTree Γ q ↔ DisjEntailsIn (fun _ => True) Γ q := by
  classical
  let := Fintype.ofFinite V
  have hvs : ∀ v : V, v ∈ Finset.univ.toList := fun v => Finset.mem_toList.mpr (Finset.mem_univ v)
  exact (disjEntailsIn_regular_iff_guarded hvs Γ q).trans
    (Full.Reduction.disjEntails_regular_iff.trans (disjEntailsIn_iff_guarded hvs Γ q).symm)
end DeciSigma1.Entailment
