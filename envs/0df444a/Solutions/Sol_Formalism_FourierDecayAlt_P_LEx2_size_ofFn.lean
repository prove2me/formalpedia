-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.size_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:08.244374+00:00
-- url     : https://prove2.me/submissions/6df0e59f-725d-4084-9377-12734be8339f

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (S : Sys) (N : ℕ) (sg : Fin N → Bool) (Y : Fin N → ℝ) :
    S.size (List.ofFn fun a => (sg a, Y a)) = ∏ a, |S.P (Y a)| := by
  unfold Sys.size
  rw [List.map_ofFn, List.prod_ofFn]
  rfl
end Formalism.FourierDecayAlt.P.LEx2
