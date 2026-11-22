-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.prj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:28.950817+00:00
-- url     : https://prove2.me/submissions/5ccbb5f4-6787-4f85-8480-20b2eb93e100

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
theorem _root_.solution (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) (p : P × ι × Fin 2) :
    prj v w p = if p.1 = v then w p else 0 := rfl
end Formalism.HN.PlaceDecomposition
