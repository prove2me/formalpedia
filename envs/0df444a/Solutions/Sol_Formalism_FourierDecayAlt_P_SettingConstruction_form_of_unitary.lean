-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.form_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:26:24.611555+00:00
-- url     : https://prove2.me/submissions/686d33c6-afa6-48e5-be3b-4b85ee9424c7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_mulVec

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
theorem _root_.solution {g : Matrix ι ι ℂ} (h : gᴴ * H * g = H) (x y : ι → ℂ) : herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by
  rw [herm_mulVec, h]
end Formalism.FourierDecayAlt.P.SettingConstruction
