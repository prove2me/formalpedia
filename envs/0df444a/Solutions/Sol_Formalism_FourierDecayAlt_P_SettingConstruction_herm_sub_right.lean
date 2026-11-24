-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.herm_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:26:25.6618+00:00
-- url     : https://prove2.me/submissions/7786264a-c9cd-4cb1-b1a1-ce94e2946135

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
theorem _root_.solution (u w w' : ι → ℂ) : herm H u (w - w') = herm H u w - herm H u w' := by
  simp [herm, sub_dotProduct]
end Formalism.FourierDecayAlt.P.SettingConstruction
