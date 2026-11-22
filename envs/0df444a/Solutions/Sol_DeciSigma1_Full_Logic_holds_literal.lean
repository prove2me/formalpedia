-- Prove2me | solution 1 for DeciSigma1.Full.Logic.holds_literal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:22:04.727597+00:00
-- url     : https://prove2.me/submissions/f9fbd5c6-fc8c-4544-998f-9ef39ee71589

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Theorems.Thm_DeciSigma1_Full_Logic_holds_eq_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Logic
open DeciSigma1.Constraints DeciSigma1.Logic DeciSigma1.Semantics
variable {n k m : ℕ} {V : Type} (c : Fin n → Bool)
namespace DeciSigma1.Full.Logic
theorem _root_.solution (ρ : V → Tree n) (l : LitT n V) :
    (literal l).Holds (interpretation c) ρ ↔ HoldsT c ρ l := by
  cases l with
  | eqBot x => exact holds_eq_iff c ρ _ _
  | eqTop x => exact holds_eq_iff c ρ _ _
  | _ => rfl
end DeciSigma1.Full.Logic
