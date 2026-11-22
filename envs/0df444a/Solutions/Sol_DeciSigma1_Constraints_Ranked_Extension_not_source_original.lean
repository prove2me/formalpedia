-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.not_source_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:52:51.358218+00:00
-- url     : https://prove2.me/submissions/59bb66ff-f475-47cd-899d-a221f0615c12

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions

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
theorem _root_.solution (e : Extension Γ ψ Source Sink rank) (u : Fin k) :
    ¬ Source (Fin.castAdd m u) := fun h => e.source_not_original h u.isLt
end Extension
end DeciSigma1.Constraints.Ranked
