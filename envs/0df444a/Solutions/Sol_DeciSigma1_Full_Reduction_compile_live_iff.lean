-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.compile_live_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:24:45.486234+00:00
-- url     : https://prove2.me/submissions/70f0051a-574b-42b2-afd5-1d805932ab28

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Theorems.Thm_DeciSigma1_Automata_foldl_take_guardedStep_ne_none_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Readers
open DeciSigma1.Constraints DeciSigma1.Full.Closure
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Full.Reduction
theorem _root_.solution (c : Fin n → Bool) (Γ : List (LitT n V)) (q : Fin k → V × V)
    (m : Fin k → Bool) (W : Fin k → List (Fin n)) (i : Fin k) {a : ℕ}
    (ha : a ≤ (W i).length) :
    (compile c Γ q m).runPrefix W i a ≠ none ↔
      ∀ a' ≤ a, EligibleWord c Γ (seedName (q i) (m i))
        (exclusionName (q i) (m i)) ((W i).take a') :=
  Automata.foldl_take_guardedStep_ne_none_iff _ _ _ _ _ ha
end DeciSigma1.Full.Reduction
