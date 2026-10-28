-- Prove2me | solution 1 for DROOptimal.Prescriptor.berge_claim
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:56:35.842375+00:00
-- url     : https://prove2.me/submissions/d14e8a63-d47a-4320-811e-7ea1d7dcc720

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Prescriptor_Pairs

open DROOptimal.Prescriptor in
theorem solution {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsCompact X)
    (chat : ↥X → DROOptimal.Predictor.Δ d → ℝ) (hchat : DROOptimal.Predictor.IsPredictor chat)
    (xhat : DROOptimal.Predictor.Δ d → ↥X) (hsel : IsArgminSelector chat xhat) :
    Continuous (fun ℙ' : DROOptimal.Predictor.Δ d => chat (xhat ℙ') ℙ') := by
  haveI : CompactSpace ↥X := isCompact_iff_compactSpace.mp hX
  have heq : (fun ℙ' : DROOptimal.Predictor.Δ d => chat (xhat ℙ') ℙ') =
      fun ℙ' => sInf ((fun x => chat x ℙ') '' Set.univ) := by
    funext P
    symm
    apply IsLeast.csInf_eq
    refine ⟨⟨xhat P, Set.mem_univ _, rfl⟩, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact hsel P x
  rw [heq]
  have hf : Continuous (Function.uncurry (fun (P : DROOptimal.Predictor.Δ d) (x : ↥X) => chat x P)) := by
    have : Function.uncurry (fun (P : DROOptimal.Predictor.Δ d) (x : ↥X) => chat x P) =
        (fun q : ↥X × DROOptimal.Predictor.Δ d => chat q.1 q.2) ∘ Prod.swap := by
      funext q; rfl
    rw [this]
    exact hchat.comp continuous_swap
  exact IsCompact.continuous_sInf (f := fun (P : DROOptimal.Predictor.Δ d) (x : ↥X) => chat x P)
    isCompact_univ hf
