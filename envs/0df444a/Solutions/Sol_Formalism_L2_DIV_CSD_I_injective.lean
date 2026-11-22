-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.I_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:35:43.470078+00:00
-- url     : https://prove2.me/submissions/8d0b3aa3-6abe-404e-83bf-36e1dfb009dd

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas

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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution : Function.Injective S.I := by
  intro x y h
  have h' : (S.basis.equivFun.symm x : S.Forms) = S.basis.equivFun.symm y := Subtype.ext h
  exact S.basis.equivFun.symm.injective h'
end Formalism.L2.DIV.CSD
