-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.Hb_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:55:44.024084+00:00
-- url     : https://prove2.me/submissions/66a73b52-4ddd-4428-9457-e60c7e152dc9

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
variable (k : ℕ)
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution : (Hb k)ᴴ = Hb k := by
  ext i j
  simp only [Hb, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all [eq_comm]
end Formalism.FourierDecayAlt.P.SettingConstruction
