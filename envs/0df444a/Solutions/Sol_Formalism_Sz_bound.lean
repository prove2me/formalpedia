-- Prove2me | solution 1 for Formalism.Sz_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:37.594748+00:00
-- url     : https://prove2.me/submissions/96bc338c-3aa7-430d-810c-9acdda457076

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau

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
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution {x X : ℝ} (hx1 : 1 ≤ x) (hxX : x ≤ X) :
    0 ≤ Sz x ∧ Sz x ≤ X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n := by
  unfold Sz
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn'.1
    have hnx : (n:ℝ) ≤ x := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith))
    apply mul_nonneg vonMangoldt_nonneg
    rw [sub_nonneg, le_div_iff₀ hnpos]
    linarith
  · rw [Finset.mul_sum]
    calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, X * Λ n := by
          apply Finset.sum_le_sum
          intro n hn
          have hn' := Finset.mem_Icc.mp hn
          have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn'.1
          have hdiv : x / n ≤ x := div_le_self (by linarith) hn1
          have hΛ : (0:ℝ) ≤ Λ n := vonMangoldt_nonneg
          nlinarith [mul_nonneg hΛ (show 0 ≤ x - x / n + 1 by linarith),
            mul_nonneg hΛ (show 0 ≤ X - x by linarith)]
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, X * Λ n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hxX)
          · intro n _ _
            exact mul_nonneg (by linarith) vonMangoldt_nonneg
end Formalism
