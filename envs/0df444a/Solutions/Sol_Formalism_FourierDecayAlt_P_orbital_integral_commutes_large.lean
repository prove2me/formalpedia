-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.orbital_integral_commutes_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:34.76632+00:00
-- url     : https://prove2.me/submissions/f4c024fd-a6e4-425f-9c3c-cf79a796cc9c

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalMeasurabilityWeakThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNormalization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralIdentities_thrW_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralIdentities_inCC_pred
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralIdentities_bigPos_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralIdentities_glev0
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralIdentities_jf_equiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_CellSmoothness_glev0
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationWordBounds_orbital_derivative_words_weak
import Theorems.Thm_Formalism_FourierDecayAlt_P_orbital_commutes_on_open_set


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.C6.JCommuteBig := by
  refine ⟨12, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D Θ A F _ hcomm hA hF
  have hthr := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.thrW_of k r (opOrder Θ) A hA
  have hF' := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.inCC_pred hF
  obtain ⟨hck, -⟩ := Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak k r Wp Wq D A (opOrder Θ) F hthr hF'
  refine ⟨?_, ?_, ?_⟩
  · intro g₀ hg₀
    have hO := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.bigPos_sub D hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hck g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hO.1, hO.2⟩
    exact ⟨U, f', hU, hgU, by exact_mod_cast hf', fun g hg hgv => hfe g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgv)⟩
  · intro p hp g _
    exact Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.jf_equiv D F p hp g
  · intro g hg
    exact (Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set k r Wp Wq D A (opOrder Θ) F Θ _ (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.bigPos_sub D) le_rfl
      hthr hF' hcomm g hg).symm
end Formalism.FourierDecayAlt.P
