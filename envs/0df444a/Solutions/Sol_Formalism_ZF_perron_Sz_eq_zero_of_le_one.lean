-- Prove2me | solution 1 for Formalism.ZF.perron_Sz_eq_zero_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:32.780157+00:00
-- url     : https://prove2.me/submissions/49184864-4965-45ec-9b2b-7d7ef67fef11

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {x : ℝ} (hx : x ≤ 1) : Formalism.Sz x = 0 := by
  unfold Formalism.Sz
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hx0 : 0 ≤ x := by
    by_contra h
    push_neg at h
    have h1 := Nat.floor_of_nonpos h.le
    omega
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 hn.2
  have hn1 : n = 1 := by
    have h1 : (n : ℝ) ≤ 1 := hnx.trans hx
    have h2 : n ≤ 1 := by exact_mod_cast h1
    omega
  subst hn1
  simp [ArithmeticFunction.vonMangoldt_apply_one]
end Formalism.ZF
