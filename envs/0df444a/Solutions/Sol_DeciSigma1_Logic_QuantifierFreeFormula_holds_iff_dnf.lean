-- Prove2me | solution 1 for DeciSigma1.Logic.QuantifierFreeFormula.holds_iff_dnf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:05:32.160962+00:00
-- url     : https://prove2.me/submissions/6ae59b56-3bbd-4ca3-a60a-28c599598fbf

module
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
public import Theorems.Thm_DeciSigma1_Logic_QuantifierFreeFormula_holds_iff_dnfWithPolarity

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} {I : Interpretation T D}
namespace DeciSigma1.Logic
namespace QuantifierFreeFormula
theorem _root_.solution (φ : QuantifierFreeFormula T V) (ρ : V → D) :
    φ.Holds I ρ ↔ ∃ c ∈ φ.dnf, c.Holds I ρ :=
  φ.holds_iff_dnfWithPolarity ρ true
end QuantifierFreeFormula
end DeciSigma1.Logic
