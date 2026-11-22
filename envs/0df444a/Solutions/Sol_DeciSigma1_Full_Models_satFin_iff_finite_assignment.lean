-- Prove2me | solution 1 for DeciSigma1.Full.Models.satFin_iff_finite_assignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:30:29.976752+00:00
-- url     : https://prove2.me/submissions/4ed9e960-589c-4cab-83fb-a63d46c51f49

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Full.Models
theorem _root_.solution {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V)) :
    SatFin c Γ ↔ ∃ σ : V → FTree n, SatT c (FTree.toTree ∘ σ) Γ := by
  constructor
  · rintro ⟨ρ, hf, hs⟩
    choose σ hσ using hf
    exact ⟨σ, (show FTree.toTree ∘ σ = ρ from funext hσ).symm ▸ hs⟩
  · rintro ⟨σ, hs⟩
    exact ⟨FTree.toTree ∘ σ, fun v => ⟨σ v, rfl⟩, hs⟩
end DeciSigma1.Full.Models
