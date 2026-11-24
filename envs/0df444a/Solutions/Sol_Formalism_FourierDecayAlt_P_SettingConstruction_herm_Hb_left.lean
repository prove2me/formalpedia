-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.herm_Hb_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:27:47.310569+00:00
-- url     : https://prove2.me/submissions/d6414ab2-2e05-4ffd-bca4-e74801a1d914

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
theorem _root_.solution (y : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    herm (Hb k) (Pi.single i 1) y = (if i = Fin.last k then -1 else 1) * star (y i) := by
  simp only [herm, dotProduct, Hb, Matrix.mulVec_diagonal]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp [mul_comm]
end Formalism.FourierDecayAlt.P.SettingConstruction
