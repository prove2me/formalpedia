-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.adK_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:50.368805+00:00
-- url     : https://prove2.me/submissions/52d94eb5-3137-44f1-8f54-e78855bb1d46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) (c : ℂ) :
    c • F ∈ AdK k r z π D := by
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U₁, F₁, hU₁, hg₁, hF₁, hE₁⟩ := hF.1 g₀ hg₀
    refine ⟨U₁, c • F₁, hU₁, hg₁, hF₁.const_smul c, ?_⟩
    intro g hg hgl
    simp [hE₁ g hg hgl]
  · intro x hx h hh
    simp [hF.2 x hx h hh, ContinuousLinearMap.comp_smul]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
