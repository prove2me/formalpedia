-- Prove2me | solution 1 for Formalism.ZF.perron_Sz_eq_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:20:26.908351+00:00
-- url     : https://prove2.me/submissions/4463d8d8-98e0-4b84-960d-622acc01b621

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Theorems.Thm_Formalism_ZF_perron_Sz_eq_Sa
import Theorems.Thm_Formalism_Sa_eq_tsum
import Theorems.Thm_Formalism_a_mxS_eq_zero


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
theorem _root_.solution {N : ℕ} {x : ℝ} (hx : x < N) :
    Formalism.Sz x = ∑ n ∈ Finset.range N, Λ n * Formalism.mxS n x := by
  rw [perron_Sz_eq_Sa, Formalism.Sa_eq_tsum _ (by simp)]
  refine tsum_eq_sum (fun n hn => ?_)
  rw [Finset.mem_range, not_lt] at hn
  have hxn : x < n := lt_of_lt_of_le hx (by exact_mod_cast hn)
  refine Formalism.a_mxS_eq_zero _ (by simp) x n ?_
  rw [Finset.mem_Icc]
  rintro ⟨h1, h2⟩
  have hx1 : 1 ≤ x := Nat.floor_pos.mp (by omega)
  have : (n : ℝ) ≤ x := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  linarith
end Formalism.ZF
