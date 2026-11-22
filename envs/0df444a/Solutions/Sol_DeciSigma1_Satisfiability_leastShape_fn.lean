-- Prove2me | solution 1 for DeciSigma1.Satisfiability.leastShape_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:07.759023+00:00
-- url     : https://prove2.me/submissions/7ccdcd3c-cdef-412b-a9f9-457c06ad7575

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
open Classical
namespace DeciSigma1.Satisfiability
theorem _root_.solution (Γ : List (LitT n V)) (x : V) (π : List (Fin n)) :
    (leastShape Γ x).fn π =
      if Semantics.IsLivePrefix (shapeLabel Γ x) π then some (shapeLabel Γ x π) else none := by
  classical
  rfl
end DeciSigma1.Satisfiability
