-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.herm_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:10:54.668119+00:00
-- url     : https://prove2.me/submissions/2af68a12-6906-444f-b231-921dfd9edcd4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_Hb_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_mid

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hb k) (wbPart k r z) (wbPart k r z) = -((Tz k r z : ℝ) : ℂ) := by
  have e := herm_mid k r z z hz hz
  have hx := herm_symm (Hb k) (Hb_herm k) (wbPart k r z) (wbPart k r z)
  simp only [Tz]
  rw [e]
  simp only [Complex.ofReal_neg, neg_neg]
  exact (Complex.conj_eq_iff_re.mp hx).symm
end Formalism.FourierDecayAlt.P.SettingConstruction
