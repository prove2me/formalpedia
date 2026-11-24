-- Prove2me | solution 1 for Formalism.HC.Landau.Gchi_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:21.711628+00:00
-- url     : https://prove2.me/submissions/14aba3af-4da4-4c52-9b52-962490accbdd

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_Sz_bound
import Theorems.Thm_Formalism_twist_bound


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
theorem _root_.solution (χ : DirichletCharacter ℂ N) (X : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → x ≤ X → |Gchi χ x| ≤ B := by
  refine ⟨|X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n| + |(deriv (LFunction χ) 1 / LFunction χ 1).re| * |X|, by positivity,
    fun x h1 hX => ?_⟩
  have hb := (Sz_bound h1 hX).2
  have hS : |Schi χ x| ≤ Sz x := by
    unfold Schi Sz
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn' := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
    have hny : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith))
    have h0 : 0 ≤ x / n - 1 := by rw [sub_nonneg, le_div_iff₀ hn0]; linarith
    rw [abs_mul, abs_of_nonneg h0]
    have := twist_bound χ n
    rw [one_mul] at this
    exact mul_le_mul_of_nonneg_right this h0
  unfold Gchi
  refine (abs_add_le _ _).trans (add_le_add (hS.trans (hb.trans (le_abs_self _))) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg (by linarith)]; exact hX.trans (le_abs_self _)) (abs_nonneg _)
end Formalism.HC.Landau
