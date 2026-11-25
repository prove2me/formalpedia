-- Prove2me | solution 1 for Formalism.L2.Col.GSD.trivOne_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:45.034081+00:00
-- url     : https://prove2.me/submissions/9a83a78f-3d00-47da-b727-a6f63b4dbf9c

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
theorem _root_.solution [Nonempty D] : trivOne K G D ≠ 0 := by
  intro h
  obtain ⟨d⟩ := ‹Nonempty D›
  have h' := congrArg (fun φ : (triv K G D).EqFun => (φ : D → K) d) h
  simp [trivOne] at h'
end Formalism.L2.Col.GSD
