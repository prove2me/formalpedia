-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.hasCountermodelIn_iff_exists_seedConsistency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:30:49.915847+00:00
-- url     : https://prove2.me/submissions/86288bd5-dc6b-4c3a-9f6e-719303dfdc44

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Reduction_SeedConsistency_realizes
public import Theorems.Thm_DeciSigma1_Full_Reduction_Realizes_seedConsistency
public import Theorems.Thm_DeciSigma1_Full_failures_iff_exists_leaf_witnesses


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Reduction
theorem _root_.solution (hs : ∃ ρ, SatT c ρ Γ) (q : Fin k → V × V) :
    HasCountermodelIn (fun _ => True) c Γ q ↔
      ∃ (m : Fin k → Bool) (W : Fin k → List (Fin n)),
        SeedConsistency c Γ (fun i => seed (q i) (m i) (W i))
          (fun i => exclusion (q i) (m i) (W i)) := by
  constructor
  · rintro ⟨ρ, _, hρ, hq⟩
    obtain ⟨m, W, hw⟩ := (failures_iff_exists_leaf_witnesses c ρ q).mp hq
    exact ⟨m, W, Realizes.seedConsistency ⟨ρ, hρ, hw⟩⟩
  · rintro ⟨m, W, h⟩
    obtain ⟨ρ, hρ, hw⟩ := h.realizes hs
    exact ⟨ρ, fun _ => trivial, hρ, (failures_iff_exists_leaf_witnesses c ρ q).mpr ⟨m, W, hw⟩⟩
end DeciSigma1.Full.Reduction
