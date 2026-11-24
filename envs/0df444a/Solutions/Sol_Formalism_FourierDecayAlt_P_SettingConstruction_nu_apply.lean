-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.nu_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:27:49.642938+00:00
-- url     : https://prove2.me/submissions/b7e81234-9ab6-4f2c-b458-7e2c471d8e38

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
theorem _root_.solution (w s : ℂ) (i j : Fin (k + 1)) :
    nu k w s i j = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j +
      ((star w - 1) * (Pi.single 0 1 : Fin (k + 1) → ℂ) i + s * (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) i) *
        (Pi.single 0 1 : Fin (k + 1) → ℂ) j +
      (s * (Pi.single 0 1 : Fin (k + 1) → ℂ) i + (w - 1) * (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) i) *
        (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) j := by
  simp [nu, Matrix.add_apply, Matrix.vecMulVec_apply]
end Formalism.FourierDecayAlt.P.SettingConstruction
