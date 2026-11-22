-- Prove2me | solution 1 for Formalism.L2.Col.GSD.wt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:15.339662+00:00
-- url     : https://prove2.me/submissions/644da0c8-5499-458b-88eb-9c5ac1333e84

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (S : GSD K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (h : S.Ok) (s : S.Sec) (c : S.Cl) :
    (S.toCSDOf h s).wt c = Nat.card (MulAction.stabilizer S.G (s.rep c)) := by
  unfold CSD.wt
  exact Fintype.card_eq_nat_card
end Formalism.L2.Col.GSD
