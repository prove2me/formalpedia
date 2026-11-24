-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.herm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:26:01.321069+00:00
-- url     : https://prove2.me/submissions/0ba14943-71dc-4386-96d8-fc6512c49f45

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
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (hH : Hᴴ = H) (u w : ι → ℂ) : star (herm H u w) = herm H w u := by
  simp only [herm]
  rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
end Formalism.FourierDecayAlt.P.SettingConstruction
