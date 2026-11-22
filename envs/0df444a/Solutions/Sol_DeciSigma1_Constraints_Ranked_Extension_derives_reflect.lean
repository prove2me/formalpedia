-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.derives_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:11:19.816952+00:00
-- url     : https://prove2.me/submissions/fa64d605-c493-46d1-a4a9-4b3444e0e7fd

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_source_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_sink_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_middle_original

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Ranked
variable {n k m : ℕ}
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}
namespace DeciSigma1.Constraints.Ranked
namespace Extension
theorem _root_.solution (e : Extension Γ ψ Source Sink rank)
    {a b : Fin (k + m)} (h : Derives ψ a b) :
    ∀ u v : Fin k, a = Fin.castAdd m u → b = Fin.castAdd m v → Derives Γ u v := by
  induction h with
  | refl a =>
    intro u v hu hv
    have he : u = v := Fin.castAdd_injective _ _ (hu.symm.trans hv)
    subst v; exact .refl _
  | lit hl =>
    rintro u v rfl rfl
    obtain ⟨u', v', hl', hu, hv⟩ := e.copy _ _ hl
    have h₁ := Fin.castAdd_injective _ _ hu
    have h₂ := Fin.castAdd_injective _ _ hv
    subst u'; subst v'
    exact .lit hl'
  | trans hl hr ih ih' =>
    rintro u v rfl rfl
    obtain ⟨w, hw⟩ := e.middle_original hl hr
    exact .trans (ih u w rfl hw) (ih' w v hw rfl)
  | @decomp a b z w i hl _ hu ih =>
    rintro u v ha hb
    rcases e.lower _ _ hl with ⟨a', z', hl', rfl, rfl⟩ | ⟨hs, _⟩
    · rcases e.upper _ _ hu with ⟨w', b', hu', rfl, rfl⟩ | ⟨ht, _⟩
      · have h₁ : a' i = u := Fin.castAdd_injective _ _ ha
        have h₂ : b' i = v := Fin.castAdd_injective _ _ hb
        subst u; subst v
        exact .decomp i hl' (ih _ _ rfl rfl) hu'
      · exact False.elim (e.not_sink_original v (hb ▸ (ht i).1))
    · exact False.elim (e.not_source_original u (ha ▸ (hs i).1))
end Extension
end DeciSigma1.Constraints.Ranked
