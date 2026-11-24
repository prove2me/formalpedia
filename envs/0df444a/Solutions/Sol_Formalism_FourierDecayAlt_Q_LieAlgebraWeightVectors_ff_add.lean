-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ff_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:17.39111+00:00
-- url     : https://prove2.me/submissions/f9d92b24-9f15-43d0-a828-1593d38d41f7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {J₁ J₂ : Mx k r → (Wq →L[ℂ] Wp)} (h₁ : J₁ ∈ FFl k r z z' π π' (Fin.last r) D)
    (h₂ : J₂ ∈ FFl k r z z' π π' (Fin.last r) D) : (fun x => J₁ x + J₂ x) ∈ FFl k r z z' π π' (Fin.last r) D := by
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq] at h₁ h₂ ⊢
  obtain ⟨s₁, l₁, r₁, e₁⟩ := h₁
  obtain ⟨s₂, l₂, r₂, e₂⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U₁, F₁, o₁, m₁, c₁, q₁⟩ := s₁ g₀ hg₀
    obtain ⟨U₂, F₂, o₂, m₂, c₂, q₂⟩ := s₂ g₀ hg₀
    refine ⟨U₁ ∩ U₂, fun x => F₁ x + F₂ x, o₁.inter o₂, ⟨m₁, m₂⟩,
      (c₁.mono Set.inter_subset_left).add (c₂.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
    rw [q₁ g hg.1 hgl, q₂ g hg.2 hgl]
  · intro g hg n hn
    rw [l₁ g hg n hn, l₂ g hg n hn, smul_add]
  · intro g hg n hn
    rw [r₁ g hg n hn, r₂ g hg n hn, smul_add]
  · intro g hg h hh h' hh'
    rw [e₁ g hg h hh h' hh', e₂ g hg h hh h' hh', ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
