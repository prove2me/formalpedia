-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.nu_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:48.816264+00:00
-- url     : https://prove2.me/submissions/a8ff7c30-5f99-49fa-9755-d249f2a57558

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_unitary_of_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_Hb_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_Hb_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_nu_mulVec

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
theorem _root_.solution (hk : 1 ≤ k) (w s : ℂ) (hs : star s = s) (hw : s * s = w * star w - 1) :
    (nu k w s)ᴴ * Hb k * nu k w s = Hb k := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hL0 : Fin.last k ≠ (0 : Fin (k + 1)) := fun h => h0L h.symm
  apply unitary_of_form
  intro x y
  rw [nu_mulVec, nu_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_Hb_right, herm_Hb_left, herm_single]
  simp only [Hb, Matrix.diagonal_apply, h0L, hL0, if_true, if_false, star_add, star_sub, star_mul', star_one, star_star, hs]
  linear_combination (star (y (Fin.last k)) * x (Fin.last k) - star (y 0) * x 0) * hw
end Formalism.FourierDecayAlt.P.SettingConstruction
