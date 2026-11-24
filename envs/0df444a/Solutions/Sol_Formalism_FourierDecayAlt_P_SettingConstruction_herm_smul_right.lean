-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:31.221788+00:00
-- url     : https://prove2.me/submissions/2c2f5b89-4d53-41b3-b633-e72f8f35ccdd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (c : ℂ) (u w : ι → ℂ) : herm H u (c • w) = star c * herm H u w := by
  simp [herm, smul_dotProduct]
end Formalism.FourierDecayAlt.P.SettingConstruction
