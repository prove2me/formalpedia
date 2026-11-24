-- Prove2me | solution 1 for Formalism.L2.DIV.polyAction_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:48.842913+00:00
-- url     : https://prove2.me/submissions/83da46cc-6f61-46d6-8aa2-2fd27b1b3648

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
omit [NumberField K]
namespace Formalism.L2.DIV
theorem _root_.solution (lam : ι → DomWeight n) (g h : ι → GL (Fin n) K) (F : Pol K ι n) :
    actP lam (g * h) F = actP lam g (actP lam h F) :=
  congrArg (fun φ : Module.End K (Pol K ι n) => φ F) ((rhoP lam).map_mul g h)
end Formalism.L2.DIV
