-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.herm_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:05.082043+00:00
-- url     : https://prove2.me/submissions/7ae13120-b8c1-4409-aa07-c93ee707cff6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_sum_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_Hpk_mid

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
variable (k r : ℕ)
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) z z' = herm (Hb k) (wbPart k r z) (wbPart k r z') := by
  simp only [herm, dotProduct, Matrix.mulVec, wbPart, Pi.star_apply]
  rw [sum_mid k r _ ?_]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [sum_mid k r _ ?_]
    · simp only [Hpk_mid]
    · intro j hj; simp [hz j hj]
  · intro i hi; simp [hz' i hi]
end Formalism.FourierDecayAlt.P.SettingConstruction
