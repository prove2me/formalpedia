-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Sec.exists_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:31.253211+00:00
-- url     : https://prove2.me/submissions/b8d27165-96c9-4cf3-ac69-4cb853a11358

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
variable {S}
namespace Formalism.L2.Col.GSD
namespace Sec
theorem _root_.solution (s s' : S.Sec) (c : S.Cl) : ∃ g : S.G, g • s.rep c = s'.rep c := by
  exact (S.cls_eq_iff _ _).mp ((s'.spec c).trans (s.spec c).symm)
end Sec
end Formalism.L2.Col.GSD
