-- Prove2me | solution 1 for DeciSigma1.Full.Models.Signed.FinitePinning.pins_signDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:32:15.836677+00:00
-- url     : https://prove2.me/submissions/12b054ab-f997-45d2-a297-b757b85d26cf

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_pins_iff
public import Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_pin_signDual_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}
open DeciSigma1.Full.Models.Signed.FinitePinning
variable {V : Type*}
namespace DeciSigma1.Full.Models.Signed.FinitePinning
theorem _root_.solution {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → Semantics.Tree n} (h : ∀ p ∈ pins c B, p.Holds A) :
    ∀ p ∈ pins c B, p.Holds (Constraints.Signed.dual A) := by
  rw [pins_iff] at h ⊢
  intro b hb s
  exact (pin_signDual_iff c b s A).mpr (h b hb (!s))
end DeciSigma1.Full.Models.Signed.FinitePinning
