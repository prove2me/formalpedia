-- Prove2me | solution 1 for Formalism.DivisionValues.RowsOrigin.univ_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:30.589936+00:00
-- url     : https://prove2.me/submissions/0c32fd55-64c1-4867-8bd2-3257c19cf96f

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.RowsOrigin
namespace Formalism.DivisionValues.RowsOrigin
theorem _root_.solution {n : ℕ} (g : Fin (n + 2) → ℕ) :
    (Finset.univ : Finset (Fin (n + 2))).val.map g =
      g 0 ::ₘ g (Fin.last (n + 1)) ::ₘ
        ((Finset.univ : Finset (Fin n)).val.map fun i => g i.castSucc.succ) := by
  rw [Fin.univ_succ]
  simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val, Multiset.map_map]
  congr 1
  rw [Fin.univ_castSuccEmb]
  simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val, Multiset.map_map]
  rfl
end Formalism.DivisionValues.RowsOrigin
