-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.compile_liveAlong_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:18.398003+00:00
-- url     : https://prove2.me/submissions/5ea770d8-685f-4f50-ab59-cd933841fd13

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Theorems.Thm_DeciSigma1_Full_Reduction_compile_live_iff
public import Theorems.Thm_DeciSigma1_Full_Reduction_eligibleWord_prefixes_iff
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


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
theorem _root_.solution (W : Fin k → List (Fin n)) (i : Fin k) :
    (∀ a ≤ (W i).length, (compile c Γ q m).runPrefix W i a ≠ none) ↔
      exclusion (q i) (m i) (W i) ∉ leastClosure c Γ ∧
        flipC (seed (q i) (m i) (W i)) ∉ leastClosure c Γ := by
  have hg := eligibleWord_prefixes_iff (c := c) (Γ := Γ)
    (seedName (q i) (m i)) (exclusionName (q i) (m i)) (W i)
  change (∀ a ≤ (W i).length, (compile c Γ q m).runPrefix W i a ≠ none) ↔ _
  apply Iff.trans ?_ hg
  constructor
  · intro h
    exact (compile_live_iff c Γ q m W i le_rfl).mp (h _ le_rfl)
  · intro h a ha
    exact (compile_live_iff c Γ q m W i ha).mpr (fun b hb => h b (hb.trans ha))
end DeciSigma1.Full.Reduction
