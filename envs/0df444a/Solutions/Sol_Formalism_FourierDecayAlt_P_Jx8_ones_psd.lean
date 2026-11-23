-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.ones_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:39.846438+00:00
-- url     : https://prove2.me/submissions/6f42d010-89dd-4ec2-92c8-13f32f2c0ae2

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution {α : Type} (F : Finset α) : TB.PSDOn F (fun _ _ : α => (1 : ℂ)) := by
  unfold TB.PSDOn
  have := Matrix.posSemidef_vecMulVec_self_star (fun _ : F => (1 : ℂ))
  convert this using 1
  ext x y; simp [Matrix.vecMulVec]
end Formalism.FourierDecayAlt.P.Jx8
