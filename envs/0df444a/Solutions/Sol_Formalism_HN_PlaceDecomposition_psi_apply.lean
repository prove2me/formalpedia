-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.psi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:13.087124+00:00
-- url     : https://prove2.me/submissions/7732a5e8-7a0e-472f-a908-08be43984209

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (v : P) (z : ι → ℂ) (p : P × ι × Fin 2) :
    psi v z p = if p.1 = v then (if p.2.2 = 0 then (z p.2.1).re else (z p.2.1).im) else 0 := rfl
end Formalism.HN.PlaceDecomposition
