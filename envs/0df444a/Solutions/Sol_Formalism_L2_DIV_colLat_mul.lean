-- Prove2me | solution 1 for Formalism.L2.DIV.colLat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:58.75921+00:00
-- url     : https://prove2.me/submissions/7ba79536-0cb0-4aa5-b734-4c221bbad014

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
namespace Formalism.L2.DIV
theorem _root_.solution (g B : GL (Fin n) K) : colLat (g * B) = gLat g (colLat B) := by
  unfold colLat gLat
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
end Formalism.L2.DIV
