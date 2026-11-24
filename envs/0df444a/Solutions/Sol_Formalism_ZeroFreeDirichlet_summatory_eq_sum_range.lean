-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.summatory_eq_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:17.050933+00:00
-- url     : https://prove2.me/submissions/13188c76-2905-4a00-8ea8-7c8e55c35fc6

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
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
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {a : ℕ → ℝ} (ha0 : a 0 = 0) {N : ℕ} {x : ℝ} (hx : x < N) :
    Formalism.Sa a x = ∑ n ∈ Finset.range N, a n * Formalism.mxS n x := by
  rw [Formalism.Sa_eq_tsum _ ha0]
  refine tsum_eq_sum (fun n hn => ?_)
  rw [Finset.mem_range, not_lt] at hn
  have hxn : x < n := lt_of_lt_of_le hx (by exact_mod_cast hn)
  refine Formalism.a_mxS_eq_zero _ ha0 x n ?_
  rw [Finset.mem_Icc]
  rintro ⟨h1, h2⟩
  have hx1 : 1 ≤ x := Nat.floor_pos.mp (by omega)
  have : (n : ℝ) ≤ x := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  linarith
end Formalism.ZeroFreeDirichlet
