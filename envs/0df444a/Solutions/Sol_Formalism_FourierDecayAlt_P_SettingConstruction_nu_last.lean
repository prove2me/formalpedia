-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.nu_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:27:50.465507+00:00
-- url     : https://prove2.me/submissions/02b7ea4a-096a-4ec0-a4f6-df0642e30a29

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_Hb_right
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
theorem _root_.solution (hk : 1 ≤ k) (w s : ℂ) : herm (Hb k) (nu k w s *ᵥ Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1) = -w := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [herm_Hb_right, nu_mulVec]
  simp [Pi.single_apply, h0L, h0L.symm]
end Formalism.FourierDecayAlt.P.SettingConstruction
