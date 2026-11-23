-- Prove2me | solution 1 for Formalism.Schi_eq_Sa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:03.689468+00:00
-- url     : https://prove2.me/submissions/5c48582b-8d51-4080-9a5b-5f270b641dc8

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Schi χ = Sa (fun n => Λ n * (χ n).re) := rfl
end Formalism
