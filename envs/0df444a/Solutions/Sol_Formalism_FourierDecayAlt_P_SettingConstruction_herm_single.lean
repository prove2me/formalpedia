-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.herm_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:53.236921+00:00
-- url     : https://prove2.me/submissions/fe9206ad-8ea6-4768-a361-97b4b49cfe63

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
variable [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (i j : ι) : herm H (Pi.single j 1) (Pi.single i 1) = H i j := by
  simp [herm, dotProduct, Matrix.mulVec, Pi.single_apply]
end Formalism.FourierDecayAlt.P.SettingConstruction
