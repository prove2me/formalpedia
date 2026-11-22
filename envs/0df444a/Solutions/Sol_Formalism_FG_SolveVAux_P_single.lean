-- Prove2me | solution 1 for Formalism.FG.SolveVAux.P_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:12.231617+00:00
-- url     : https://prove2.me/submissions/ec50c4f6-9951-4870-aa46-f6fbe53c5114

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution (k : ι → MvPowerSeries τ R) (i : ι) (n : ℕ) :
    P k (Finsupp.single i n) = k i ^ n :=
  Finsupp.prod_single_index (pow_zero _)
end Formalism.FG.SolveVAux
