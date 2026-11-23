-- Prove2me | solution 1 for Formalism.L2.Col.GSD.triv_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:19.323847+00:00
-- url     : https://prove2.me/submissions/0f08f26c-aaf9-4e95-9455-4e5d0f2af560

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
theorem _root_.solution (h1 : Finite (MulAction.orbitRel.Quotient G D)) (h2 : ∀ d : D, Finite (MulAction.stabilizer G d)) :
    (triv K G D).Ok where
  fin_orb := h1
  fin_stab := h2
  nab_smul := by
    intro g d
    show (1 : Submodule (𝓞 K) K) = (1 : Submodule (𝓞 K) K).map ((1 : Module.End K K).restrictScalars (𝓞 K))
    exact (Submodule.map_id _).symm
  del_smul := by
    intro g d
    show (1 : Submodule (𝓞 K) K) = (1 : Submodule (𝓞 K) K).map ((1 : Module.End K K).restrictScalars (𝓞 K))
    exact (Submodule.map_id _).symm
  inv := by
    intro g x y
    rfl
end Formalism.L2.Col.GSD
