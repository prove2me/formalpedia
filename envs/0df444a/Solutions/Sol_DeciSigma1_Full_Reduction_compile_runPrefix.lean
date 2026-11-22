-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.compile_runPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:16:21.530183+00:00
-- url     : https://prove2.me/submissions/1ea32f49-3e01-4261-ae37-b4c5bd83305b

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Theorems.Thm_DeciSigma1_Automata_foldl_guardedStep_eq_some


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
    (h : (compile c Γ q m).runPrefix W i a ≠ none) :
    (compile c Γ q m).runPrefix W i a =
      some (Automata.upperRun (signed c Γ) (seedName (q i) (m i)) ((W i).take a),
          Automata.lowerRun (signed c Γ) (exclusionName (q i) (m i)) ((W i).take a)) :=
  Automata.foldl_guardedStep_eq_some _ _ _ _ _ h
end DeciSigma1.Full.Reduction
