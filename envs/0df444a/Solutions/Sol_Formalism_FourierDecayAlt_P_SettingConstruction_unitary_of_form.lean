-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.unitary_of_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:21.600946+00:00
-- url     : https://prove2.me/submissions/67bea93d-f7e5-485b-991a-7c8ed15bcaec

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_single

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
theorem _root_.solution (g : Matrix ι ι ℂ) (h : ∀ x y, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) : gᴴ * H * g = H := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rwa [herm_mulVec, herm_single, herm_single] at this
end Formalism.FourierDecayAlt.P.SettingConstruction
