-- Prove2me | solution 1 for Formalism.HadamardInequality.P.hadamard_maximum_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:02.907993+00:00
-- url     : https://prove2.me/submissions/9b4b6a38-9c8a-4988-8988-2207c6cb130c

import Mathlib
import Definitions.Def_Formalism_GelfandTransference_Statement
import Definitions.Def_Lemmata_DetNormLeProdRows_DetNormLeProdRows
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Theorems.Thm_Formalism_HadamardInequality_P_hadamard_inequality_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.HadamardInequality Formalism.HadamardInequality.P
namespace Formalism.HadamardInequality.P
theorem _root_.solution : Formalism.HadamardInequality.HadamardMax := by
  unfold Formalism.HadamardInequality.HadamardMax
  intro ρ A M hM
  have hH := hadamard_inequality_holds
  unfold Formalism.HadamardInequality.Hadamard at hH
  refine (hH ρ A).trans ?_
  calc ∏ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∏ _i : Fin ρ, ((ρ : ℝ) * M ^ 2) := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => by positivity)
          fun i _ => ?_
        calc ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _j : Fin ρ, M ^ 2 := by
              refine Finset.sum_le_sum fun j _ => ?_
              have hij := hM i j
              gcongr
          _ = (ρ : ℝ) * M ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((ρ : ℝ) * M ^ 2) ^ ρ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end Formalism.HadamardInequality.P
