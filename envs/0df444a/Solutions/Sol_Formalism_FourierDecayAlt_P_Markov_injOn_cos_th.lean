-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.injOn_cos_th
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:20.702155+00:00
-- url     : https://prove2.me/submissions/05d114b2-962f-49d8-b7a1-b285c083311c

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution (n : ℕ) : Set.InjOn (fun k => cos (th n k)) (Finset.range n : Finset ℕ) :=
  (Finset.range n).nodup_map_iff_injOn.mp (Chebyshev.roots_T_real_nodup n)
end Formalism.FourierDecayAlt.P.Markov
