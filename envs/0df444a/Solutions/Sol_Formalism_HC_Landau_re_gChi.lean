-- Prove2me | solution 1 for Formalism.HC.Landau.re_gChi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:56.46962+00:00
-- url     : https://prove2.me/submissions/995a79ef-3f70-4294-956e-84b30f5499e1

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
open DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Landau
theorem _root_.solution (ξ : DirichletCharacter ℂ N) (h : ξ ≠ 1) (y : ℝ) : (An.gChi ξ y).re = Gchi ξ y := by
  unfold An.gChi Gchi Schi An.sumLamChi An.logDerivativeAtOne
  rw [if_neg h, add_re, re_sum, re_ofReal_mul, mul_comm y]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
  have hy : (1 : ℝ) ≤ y := by
    have : 1 ≤ ⌊y⌋₊ := hn'.1.trans hn'.2
    exact_mod_cast (Nat.one_le_floor_iff y).1 this
  have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith))
  have h0 : 0 ≤ y / n - 1 := by rw [sub_nonneg, le_div_iff₀ hn0]; linarith
  rw [max_eq_left h0, re_mul_ofReal, re_ofReal_mul]
end Formalism.HC.Landau
