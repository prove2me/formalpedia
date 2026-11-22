-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.hasCountermodelIn_iff_exists_hole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:41.929268+00:00
-- url     : https://prove2.me/submissions/1ab18267-26eb-4ba1-a946-62be5b2a34ad

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Theorems.Thm_DeciSigma1_Full_Reduction_hole_iff_terminalRootConditions
public import Theorems.Thm_DeciSigma1_Full_Reduction_hasCountermodelIn_iff_exists_seedConsistency
public import Theorems.Thm_DeciSigma1_Full_Reduction_seedConsistency_iff_terminalRootConditions


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}
namespace DeciSigma1.Full.Reduction
theorem _root_.solution (hs : ∃ ρ, SatT c ρ Γ) :
    HasCountermodelIn (fun _ => True) c Γ q ↔
      ∃ m : Fin k → Bool, ∃ W, (compile c Γ q m).IsHole W := by
  rw [hasCountermodelIn_iff_exists_seedConsistency hs q]
  apply exists_congr
  intro m
  apply exists_congr
  intro W
  rw [seedConsistency_iff_terminalRootConditions, hole_iff_terminalRootConditions]
end DeciSigma1.Full.Reduction
