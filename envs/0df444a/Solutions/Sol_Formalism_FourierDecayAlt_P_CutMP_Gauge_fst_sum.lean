-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.fst_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:00:35.273116+00:00
-- url     : https://prove2.me/submissions/9e8c543b-05dc-485e-99c8-33bb629de367

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
theorem _root_.solution {ι : Type} (s : Finset ι) (x : ι → (MA.DQ P).Pr) : (∑ i ∈ s, x i).1 = ∑ i ∈ s, (x i).1 :=
  map_sum (fstHom P) x s
end Formalism.FourierDecayAlt.P.CutMP.Gauge
