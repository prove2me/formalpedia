-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.satFin_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:22:42.622288+00:00
-- url     : https://prove2.me/submissions/0bb6c657-d6b2-415f-97ba-9ec3a07dbf0d

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_restrict_sat
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_cycleClash_iff
public import Theorems.Thm_DeciSigma1_Constraints_LabelClash_unsatisfiable
public import Theorems.Thm_DeciSigma1_Satisfiability_satFin_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.Ranked
open DeciSigma1.Constraints.Covariant DeciSigma1.Satisfiability DeciSigma1.Semantics
variable {n k m : ℕ}
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}
namespace DeciSigma1.Constraints.Ranked
namespace Extension
theorem _root_.solution (e : Extension Γ ψ Source Sink rank) :
    (∃ σ : Fin (k + m) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ψ) ↔
      (∃ ρ', Covariant.Sat ρ' ψ) ∧ ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨_, hσ⟩, ⟨σ ∘ Fin.castAdd m, e.restrict_sat hσ⟩⟩
  · rintro ⟨⟨ρ', hρ'⟩, hf⟩
    apply Satisfiability.satFin_iff.mpr
    exact ⟨fun hl => hl.unsatisfiable ⟨ρ', hρ'⟩,
      fun hc => (Satisfiability.satFin_iff.mp hf).2 (e.cycleClash_iff.mp hc)⟩
end Extension
end DeciSigma1.Constraints.Ranked
