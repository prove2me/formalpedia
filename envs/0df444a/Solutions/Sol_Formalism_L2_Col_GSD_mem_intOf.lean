-- Prove2me | solution 1 for Formalism.L2.Col.GSD.mem_intOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:35.918021+00:00
-- url     : https://prove2.me/submissions/161e2c49-6710-4ba9-9995-8593f62243cd

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
theorem _root_.solution (N : S.D → Submodule (𝓞 K) S.V) (φ : S.EqFun) :
    φ ∈ S.intOf N ↔ ∀ d, (φ : S.D → S.V) d ∈ N d := by
  exact Iff.rfl
end Formalism.L2.Col.GSD
