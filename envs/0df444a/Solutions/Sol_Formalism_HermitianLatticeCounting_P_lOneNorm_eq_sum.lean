-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lOneNorm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:29.410081+00:00
-- url     : https://prove2.me/submissions/552610f3-a3fd-499e-991c-6652664d3cf0

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {P : Type} (a : P →₀ ℂ) (s : Finset P) (hs : a.support ⊆ s) :
    lOneNorm a = ∑ i ∈ s, ‖a i‖ :=
  Finsupp.sum_of_support_subset a hs _ (by simp)
end Formalism.HermitianLatticeCounting.P
