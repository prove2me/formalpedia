-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.inCC_pred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:40:18.353433+00:00
-- url     : https://prove2.me/submissions/f6eae72e-139a-4750-aa79-4d69e8ad0a2e

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalMeasurabilityWeakThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNormalization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralIdentities

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
theorem _root_.solution {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {o : ℕ}
    {F : Mat k r → E} (h : InCC A (o + 1) F) : InCC A o F := by
  obtain ⟨c, hck, hb⟩ := h
  refine ⟨c, ?_, fun u v hu hv hl g hg => hb u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hck g₀ hg₀
  exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast Nat.le_succ o), hfe⟩
end Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
