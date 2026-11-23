-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.affine_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:22.621853+00:00
-- url     : https://prove2.me/submissions/7ca3c8db-7ddd-4dc2-a60e-ff42de58ea3c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_map_mul_vol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.AffineChange := by
  intro β α γ hα
  have h1 : (fun ρ : ℂ => α * ρ + γ) = (fun x => x + γ) ∘ (fun ρ : ℂ => α * ρ) := rfl
  unfold mu
  rw [Measure.map_smul, h1, ← Measure.map_map (measurable_add_const γ) (measurable_const_mul α),
    map_mul_vol α hα, Measure.map_smul, map_add_right_eq_self]
  rw [smul_comm]
  congr 1
end Formalism.FourierDecayAlt.P
