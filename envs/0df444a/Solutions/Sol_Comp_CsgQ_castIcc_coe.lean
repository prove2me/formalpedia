-- Prove2me | solution 1 for Comp.CsgQ.castIcc_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:52:53.461272+00:00
-- url     : https://prove2.me/submissions/ab22822e-cfd3-474c-999a-f550e677c53f

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S : Type*}
namespace Comp.CsgQ
theorem _root_.solution (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (s : S) :
    ((castIcc v h0 h1 s : ℝ)) = ((v s : ℚ) : ℝ) := rfl
end Comp.CsgQ
