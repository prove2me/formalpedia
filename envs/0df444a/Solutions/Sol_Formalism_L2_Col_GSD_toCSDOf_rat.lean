-- Prove2me | solution 1 for Formalism.L2.Col.GSD.toCSDOf_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:59.712123+00:00
-- url     : https://prove2.me/submissions/1c302119-a3fa-42aa-adf4-e4bdebd31d5b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV
open Formalism.L2.Col.GSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (h : S.Ok) (R : S.Rat) (s : S.Sec) : (S.toCSDOf h s).Rat where
  pair_rat := R.pair_rat
  act_rat := fun c γ i j => R.act_rat ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) i j
  pos := R.pos
end Formalism.L2.Col.GSD
