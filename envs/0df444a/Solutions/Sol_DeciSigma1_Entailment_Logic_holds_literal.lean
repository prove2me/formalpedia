-- Prove2me | solution 1 for DeciSigma1.Entailment.Logic.holds_literal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:23:12.299712+00:00
-- url     : https://prove2.me/submissions/d770a59a-5c03-4e44-8707-e0d3c307cfe1

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Encodings

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment DeciSigma1.Entailment.Logic
open DeciSigma1.Constraints.TopFree DeciSigma1.Logic DeciSigma1.Semantics
variable {n k m : ℕ} {V : Type}
namespace DeciSigma1.Entailment.Logic
theorem _root_.solution (ρ : V → PrefixSet n) (l : Lit n V) :
    (literal l).Holds (interpretation n) ρ ↔ l.Holds ρ := by
  cases l with
  | eqBot x => exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  | _ => rfl
end DeciSigma1.Entailment.Logic
