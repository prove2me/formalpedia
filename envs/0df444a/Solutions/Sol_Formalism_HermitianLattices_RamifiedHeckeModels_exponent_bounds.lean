-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.exponent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:01.649089+00:00
-- url     : https://prove2.me/submissions/50dffff6-881f-403b-b2a6-351040e4adb3

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LengthQuotientLeOfLatticeSandwich
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution : TableauExponentRange := by
  intro μ T j
  classical
  calc (μ.cells.filter (fun c => T c.1 c.2 = j)).card
      ≤ (Finset.range (μ.rowLen 0)).card := by

        apply Finset.card_le_card_of_injOn (fun c => c.2)
        · intro c hc
          simp only [Finset.coe_filter, Set.mem_setOf_eq, YoungDiagram.mem_cells] at hc
          simp only [Finset.coe_range, Set.mem_Iio]
          rw [← YoungDiagram.mem_iff_lt_rowLen]
          exact μ.up_left_mem (Nat.zero_le _) le_rfl hc.1
        · rintro ⟨a, k⟩ hc ⟨b, k'⟩ hd (hk : k = k')
          subst hk
          simp only [Finset.coe_filter, Set.mem_setOf_eq, YoungDiagram.mem_cells] at hc hd
          rcases lt_trichotomy a b with hab | rfl | hab
          · have := T.col_strict hab hd.1
            omega
          · rfl
          · have := T.col_strict hab hc.1
            omega
    _ = μ.rowLen 0 := Finset.card_range _
end Formalism.HermitianLattices.RamifiedHeckeModels
