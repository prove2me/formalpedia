-- Prove2me | solution 1 for Formalism.L2.Col.GSD.trivOne_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:13:56.764551+00:00
-- url     : https://prove2.me/submissions/ca50ac87-5411-4479-a1b9-fc85c62d4003

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (K) (G D : Type) [Group G] [MulAction G D]
namespace Formalism.L2.Col.GSD
theorem _root_.solution : trivOne K G D ∈ (triv K G D).intDel := by
  intro d
  show (1 : K) ∈ (1 : Submodule (𝓞 K) K)
  exact Submodule.one_le.mp le_rfl
end Formalism.L2.Col.GSD
