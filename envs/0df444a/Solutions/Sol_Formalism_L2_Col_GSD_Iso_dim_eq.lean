-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Iso.dim_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:10:01.220805+00:00
-- url     : https://prove2.me/submissions/ba419e9c-984a-4ae6-8d58-b775f1b7d2bf

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
open Formalism.L2.Col.GSD Formalism.L2.Col.GSD.Iso
variable {S S' : GSD K} (e : GSD.Iso S S')
include e
namespace Formalism.L2.Col.GSD.Iso
theorem _root_.solution (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) :
    (S'.toCSDOf h' s').dim = (S.toCSDOf h s).dim := by
  unfold CSD.dim
  exact (((S'.resOf h' s').symm.trans e.onForms.symm).trans (S.resOf h s)).finrank_eq
end Formalism.L2.Col.GSD.Iso
