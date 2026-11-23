-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.card_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:02.538796+00:00
-- url     : https://prove2.me/submissions/8bceef2c-92f6-4796-9ca3-427b97a952af

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type*} [Field K]
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution [Fintype K] (W U : Type*) [AddCommGroup W] [Module K W] [AddCommGroup U]
    [Module K U] [Finite W] [Finite U] :
    Nat.card {f : W →ₗ[K] U // Function.Injective f} =
      ∏ j ∈ range (finrank K W), (Fintype.card K ^ finrank K U - Fintype.card K ^ j) := by
  classical
  let b := Module.finBasis K W
  have key : ∀ s : Fin (finrank K W) → U,
      LinearIndependent K s ↔ Function.Injective (b.constr K s : W →ₗ[K] U) := by
    intro s
    show Function.Injective (Finsupp.linearCombination K s) ↔ _
    have : ((b.constr K s : W →ₗ[K] U) : W → U) = (Finsupp.linearCombination K s) ∘ b.repr := by
      funext x
      rw [Basis.constr_apply, Function.comp_apply, Finsupp.linearCombination_apply]
    rw [this]
    exact (EquivLike.injective_comp b.repr _).symm
  have e : {f : W →ₗ[K] U // Function.Injective f} ≃
      {s : Fin (finrank K W) → U // LinearIndependent K s} :=
    ((b.constr K (M' := U)).toEquiv.subtypeEquiv (p := fun s => LinearIndependent K s)
      (q := fun f : W →ₗ[K] U => Function.Injective f) key).symm
  rw [Nat.card_congr e]
  by_cases hk : finrank K W ≤ finrank K U
  · rw [card_linearIndependent hk, Finset.prod_range]
  · rw [not_le] at hk
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hk) (by simp)]
    rw [Nat.card_eq_zero]; left
    constructor
    rintro ⟨s, hs⟩
    have := hs.fintype_card_le_finrank
    simp at this
    omega
end Formalism.FourierDecayAlt.P.S3x4
