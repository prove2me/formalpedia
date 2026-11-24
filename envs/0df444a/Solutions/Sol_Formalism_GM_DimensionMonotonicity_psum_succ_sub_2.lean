-- Prove2me | solution 2 for Formalism.GM.DimensionMonotonicity.psum_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T22:53:41.586821+00:00
-- url     : https://prove2.me/submissions/fef9525f-afb2-4690-8230-3ba8ae04462c

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
open Finset
variable {r : ℕ}

theorem solution (μ : Fin r → ℤ) (c : Fin r) : psum μ (c + 1) - psum μ c = μ c := by
  unfold psum
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single c]
  · simp
  · intro b _ hbc
    have hv : b.val ≠ c.val := fun e => hbc (Fin.ext e)
    by_cases h : b.val < c.val
    · simp [h, show b.val < c.val + 1 by omega]
    · simp [h, show ¬ b.val < c.val + 1 by omega]
  · simp
