-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.herm_Hb_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:25:57.07262+00:00
-- url     : https://prove2.me/submissions/5d96af24-8f06-4b16-a30c-79e0df9e1a5a

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
theorem _root_.solution (x : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    herm (Hb k) x (Pi.single i 1) = (if i = Fin.last k then -1 else 1) * x i := by
  simp only [herm, dotProduct, Hb, Matrix.mulVec_diagonal]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp
end Formalism.FourierDecayAlt.P.SettingConstruction
