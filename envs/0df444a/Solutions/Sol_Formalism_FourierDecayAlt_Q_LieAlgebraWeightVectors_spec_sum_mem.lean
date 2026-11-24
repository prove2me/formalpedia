-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.spec_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:42.735029+00:00
-- url     : https://prove2.me/submissions/aecebfee-c2f8-401c-9a30-f07f0298b736

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SpecAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {X : Type*}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {β : Type*} (𝓕 : Set (X → (Wq →L[ℂ] Wp)))
    (h0 : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ 𝓕)
    (hadd : ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (fun x => F₁ x + F₂ x) ∈ 𝓕)
    (f : β → X → (Wq →L[ℂ] Wp)) (s : Finset β) (hf : ∀ i ∈ s, f i ∈ 𝓕) :
    (fun x => ∑ i ∈ s, f i x) ∈ 𝓕 := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun x => ∑ i ∈ (∅ : Finset β), f i x) = fun _ => (0 : Wq →L[ℂ] Wp) := by
      funext x; simp
    rw [e]; exact h0
  · intro a s ha ih hf
    have e : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x; rw [Finset.sum_insert ha]
    rw [e]
    exact hadd _ (hf a (Finset.mem_insert_self a s)) _
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
