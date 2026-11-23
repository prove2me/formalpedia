-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.domMonoE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:40.150336+00:00
-- url     : https://prove2.me/submissions/2bf830d1-b0c3-4dd8-8d6c-39a5c1c8d06c

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution : DomMonoE := by
  intro E W _ D T Th e' hK he hD i s hs hsi hi
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hi
  refine ⟨h1, h2, fun S hS hSd => ?_⟩
  have ha := psd_add (h3 S hS hSd)
    (psd_smul (e' i - D.e i) (by linarith [he i]) (hK (i - s) (T.X (i - s))))
  refine psd_congr (fun x _ y _ => ?_) ha
  dsimp only
  push_cast
  ring
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
