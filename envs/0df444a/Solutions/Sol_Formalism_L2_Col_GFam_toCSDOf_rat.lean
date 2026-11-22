-- Prove2me | solution 1 for Formalism.L2.Col.GFam.toCSDOf_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:48.114785+00:00
-- url     : https://prove2.me/submissions/72f6d518-c1e5-4fdb-b1cb-1e64e60fdde3

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
open Formalism.L2.Col.GFam
variable (F : GFam K)
namespace Formalism.L2.Col.GFam
theorem _root_.solution [Nonempty F.β] (h : F.Ok) (R : ∀ b, (F.mem b).Rat) (s : ∀ b, (F.mem b).Sec) :
    (F.toCSDOf h s).Rat where
  pair_rat := (R (Classical.arbitrary F.β)).pair_rat
  act_rat := fun c γ i j => (R c.1).act_rat (γ : F.G c.1) i j
  pos := (R (Classical.arbitrary F.β)).pos
end Formalism.L2.Col.GFam
