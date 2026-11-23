-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.LFunction_eq_G_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:43.864061+00:00
-- url     : https://prove2.me/submissions/5d0e4b88-fdd7-4cc1-a5af-7cf196e28f13

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_sum_Icc_eq_sum_range
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_partial_tendsto_G

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = G χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have h1 := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h2 := partial_tendsto_G χ hB (by linarith : 0 < s.re)
  refine tendsto_nhds_unique (h1.congr fun M => ?_) h2
  show ∑ n ∈ Finset.range (M + 1), LSeries.term _ s n = _
  rw [← sum_Icc_eq_sum_range _ (LSeries.term_zero _ _) M]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by
    rw [Finset.mem_Icc] at hn
    omega
  rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
end Formalism.FX.LFunctionPartialSum
