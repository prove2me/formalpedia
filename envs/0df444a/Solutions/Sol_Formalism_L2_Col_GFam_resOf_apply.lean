-- Prove2me | solution 1 for Formalism.L2.Col.GFam.resOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:45.68054+00:00
-- url     : https://prove2.me/submissions/ccf50e27-837b-4b46-8d04-770b18f4d18f

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
attribute [instance] GFam.finβ GFam.decβ GFam.addV GFam.modV GFam.modOV GFam.towV GFam.finιV GFam.decιV GFam.grpG
  GFam.actD
open Formalism.L2.Col.GFam
variable (F : GFam K)
namespace Formalism.L2.Col.GFam
theorem _root_.solution (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) (c : F.Cl) :
    (F.resOf h s φ).1 c = ((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) ((s c.1).rep c.2) := rfl
end Formalism.L2.Col.GFam
