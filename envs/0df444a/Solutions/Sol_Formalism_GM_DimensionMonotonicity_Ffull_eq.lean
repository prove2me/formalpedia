-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.Ffull_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:56.297402+00:00
-- url     : https://prove2.me/submissions/da5f8ded-93b2-4376-a163-d511831d7540

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero N] (LL : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.Ffull p LL i ρ n f = rename (fun x => (ιF N (T.pos i + 1) x.1, x.2)) (freeze p (LL.takeD (T.pos i + 1)) ρ n f) :=
  rfl
end Formalism.GM.DimensionMonotonicity
