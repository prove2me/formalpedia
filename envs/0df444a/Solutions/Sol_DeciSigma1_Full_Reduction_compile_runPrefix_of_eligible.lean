-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.compile_runPrefix_of_eligible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:21:21.500811+00:00
-- url     : https://prove2.me/submissions/41d0feb0-3c92-4803-9e1c-d74c6bb0a6e5

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Theorems.Thm_DeciSigma1_Full_Reduction_compile_runPrefix
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Readers
open DeciSigma1.Constraints DeciSigma1.Full.Closure
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
  {q : Fin k → V × V} {m : Fin k → Bool}
namespace DeciSigma1.Full.Reduction
theorem _root_.solution {W : Fin k → List (Fin n)} {i : Fin k}
    (h : (compile c Γ q m).Eligible W i) (a : Nat) :
    (compile c Γ q m).runPrefix W i a =
      some (Automata.upperRun (signed c Γ) (seedName (q i) (m i)) ((W i).take a),
        Automata.lowerRun (signed c Γ) (exclusionName (q i) (m i)) ((W i).take a)) :=
  compile_runPrefix c Γ q m W i (h.runPrefix_ne a)
end DeciSigma1.Full.Reduction
