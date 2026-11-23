-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:54.881609+00:00
-- url     : https://prove2.me/submissions/6d0d25ff-48bd-4cb5-b38d-05492389903b

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_locAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_locAt_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_exists_multiplier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
namespace Formalism.FourierDecayAlt.P.S6x6
theorem _root_.solution {L : Submodule ℤ E} (hL : IsFLattice E L)
    (S : Finset (Ideal (𝓞 (maximalRealSubfield E)))) (τ : Ideal (𝓞 (maximalRealSubfield E)) → E)
    (hS : ∀ P ∈ S, P.IsMaximal) :
    ∃ t : E, (∀ P ∈ S, t - τ P ∈ locAt E P L) ∧
      ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → P ∉ S → t ∈ locAt E P L := by
  classical
  have hex : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), ∃ e : 𝓞 (maximalRealSubfield E),
      P.IsMaximal → (algebraMap (𝓞 (maximalRealSubfield E)) E e * τ P - τ P ∈ locAt E P L ∧
      ∀ Q : Ideal (𝓞 (maximalRealSubfield E)), Q.IsMaximal → Q ≠ P →
        algebraMap (𝓞 (maximalRealSubfield E)) E e * τ P ∈ locAt E Q L) := by
    intro P
    by_cases hP : P.IsMaximal
    · obtain ⟨e, he⟩ := exists_multiplier hL P hP (τ P)
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose e he using hex
  refine ⟨∑ P ∈ S, algebraMap (𝓞 (maximalRealSubfield E)) E (e P) * τ P, ?_, ?_⟩
  · intro P hPS
    rw [← Finset.add_sum_erase S _ hPS, add_sub_right_comm]
    refine locAt_add hL (hS P hPS).isPrime (he P (hS P hPS)).1 ?_
    refine locAt_sum hL (hS P hPS).isPrime _ _ fun Q hQ => ?_
    rw [Finset.mem_erase] at hQ
    exact (he Q (hS Q hQ.2)).2 P (hS P hPS) (Ne.symm hQ.1)
  · intro P hP hPS
    refine locAt_sum hL hP.isPrime _ _ fun Q hQ => ?_
    exact (he Q (hS Q hQ)).2 P hP (fun h => hPS (h ▸ hQ))
end Formalism.FourierDecayAlt.P.S6x6
