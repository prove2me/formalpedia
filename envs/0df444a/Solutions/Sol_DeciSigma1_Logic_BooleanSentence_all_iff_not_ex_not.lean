-- Prove2me | solution 1 for DeciSigma1.Logic.BooleanSentence.all_iff_not_ex_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:33.981795+00:00
-- url     : https://prove2.me/submissions/1319ae3c-6ffa-4c8c-9148-82d35d2c78b0

module
public import Mathlib.Data.Nat.Notation
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type}
namespace DeciSigma1.Logic
namespace BooleanSentence
theorem _root_.solution (I : Interpretation T D) (C : D → Prop)
    (s : Sigma1 T) :
    (BooleanSentence.all s).HoldsIn I C ↔
        ¬ (Sigma1.mk s.variableCount (.not s.body)).HoldsIn I C := by
  simp [BooleanSentence.HoldsIn, Sigma1.HoldsIn, QuantifierFreeFormula.Holds]
end BooleanSentence
end DeciSigma1.Logic
