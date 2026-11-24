-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.op_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:00:36.690359+00:00
-- url     : https://prove2.me/submissions/1c2aa472-8ae2-43b2-8c9c-ce8f9ce0ebc3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge
noncomputable section
variable (P : M.Par)
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge
theorem _root_.solution {ι : Type} (s : Finset ι) (X : ι → (MA.DQ P).Op) (g : (MA.DQ P).R) :
    (∑ i ∈ s, X i) g = ∑ i ∈ s, X i g :=
  map_sum (evalHom P g) X s
end Formalism.FourierDecayAlt.P.CutMP.Gauge
