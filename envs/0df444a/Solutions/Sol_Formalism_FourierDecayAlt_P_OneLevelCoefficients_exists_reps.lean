-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:29.212542+00:00
-- url     : https://prove2.me/submissions/ca7d2a0c-53da-49f4-8372-e0bb2ef5e8d8

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OneLevelCoefficients
open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.OneLevelCoefficients
theorem _root_.solution (L : AddSubgroup E) (S : Finset E) :
    ∃ R : Finset E, (∀ t ∈ S, ∃ t₀ ∈ R, t - t₀ ∈ L) ∧
      (∀ t₀ ∈ R, ∀ t₀' ∈ R, t₀ - t₀' ∈ L → t₀ = t₀') := by
  classical
  have hout : ∀ t : E, (((t : E ⧸ L).out : E) : E ⧸ L) = (t : E ⧸ L) :=
    fun t => QuotientAddGroup.out_eq' _
  refine ⟨S.image (fun t : E => (QuotientAddGroup.mk t : E ⧸ L).out), ?_, ?_⟩
  · intro t ht
    refine ⟨_, Finset.mem_image_of_mem _ ht, ?_⟩
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, hout, sub_self]
  · intro a ha b hb hab
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 hb
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, hout, hout, sub_eq_zero] at hab
    simp only [hab]
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
