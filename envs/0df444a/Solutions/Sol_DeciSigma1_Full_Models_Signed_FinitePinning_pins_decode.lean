-- Prove2me | solution 1 for DeciSigma1.Full.Models.Signed.FinitePinning.pins_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:45.180809+00:00
-- url     : https://prove2.me/submissions/43c78fa5-a1b0-4fc6-86ad-1e7cfa6a144c

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_pins_normalize_iff
public import Theorems.Thm_DeciSigma1_Constraints_normalized_decoded


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
    {A : V × Bool → Semantics.Tree n} (hf : Constraints.Signed.dual A = A)
    (h : ∀ p ∈ pins c B, p.Holds A) : ∀ b ∈ B, b.HoldsWithVariance c (decoded c A) := by
  apply (pins_normalize_iff c B _).mp
  rwa [normalized_decoded c hf]
end DeciSigma1.Full.Models.Signed.FinitePinning
