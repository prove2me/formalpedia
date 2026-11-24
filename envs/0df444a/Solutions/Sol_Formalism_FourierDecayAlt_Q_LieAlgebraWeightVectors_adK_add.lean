-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.adK_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:49.294731+00:00
-- url     : https://prove2.me/submissions/7127512b-a7f1-4a1e-a0d4-f854790017a9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


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
theorem _root_.solution {F G : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) (hG : G ∈ AdK k r z π D) :
    F + G ∈ AdK k r z π D := by
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U₁, F₁, hU₁, hg₁, hF₁, hE₁⟩ := hF.1 g₀ hg₀
    obtain ⟨U₂, F₂, hU₂, hg₂, hF₂, hE₂⟩ := hG.1 g₀ hg₀
    refine ⟨U₁ ∩ U₂, F₁ + F₂, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
      (hF₁.mono Set.inter_subset_left).add (hF₂.mono Set.inter_subset_right), ?_⟩
    intro g hg hgl
    simp [hE₁ g hg.1 hgl, hE₂ g hg.2 hgl]
  · intro x hx h hh
    simp [hF.2 x hx h hh, hG.2 x hx h hh, ContinuousLinearMap.comp_add]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
