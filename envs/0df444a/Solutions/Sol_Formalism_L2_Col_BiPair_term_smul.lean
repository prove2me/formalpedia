-- Prove2me | solution 1 for Formalism.L2.Col.BiPair.term_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:33.38568+00:00
-- url     : https://prove2.me/submissions/e2c10ad1-40f0-4679-af7e-f51549a4de4d

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
open Formalism.L2.Col.BiPair
variable {S S' : GSD K} (P : BiPair S S')
namespace Formalism.L2.Col.BiPair
theorem _root_.solution (φ : S.EqFun) (ψ : S'.EqFun) (g : S'.G) (d' : S'.D) :
    P.B ((φ : S.D → S.V) (P.p (g • d'))) ((ψ : S'.D → S'.V) (g • d')) =
      P.B ((φ : S.D → S.V) (P.p d')) ((ψ : S'.D → S'.V) d') := by
  rw [P.hp, φ.2, ψ.2, P.inv]
end Formalism.L2.Col.BiPair
