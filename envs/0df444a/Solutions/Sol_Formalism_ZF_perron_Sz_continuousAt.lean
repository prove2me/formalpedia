-- Prove2me | solution 1 for Formalism.ZF.perron_Sz_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:18.581098+00:00
-- url     : https://prove2.me/submissions/936dd227-6838-4067-af40-f4f86f08889b

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
theorem _root_.solution (y : ℝ) : ContinuousAt (fun x => (Formalism.Sz x : ℂ)) y := by
  have key : ∀ N : ℕ, ∀ x : ℝ, x < N →
      Formalism.Sz x = ∑ n ∈ Finset.range N, Λ n * max (x / n - 1) 0 := by
    intro N x hx
    unfold Formalism.Sz
    by_cases hx0 : 0 ≤ x
    · have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.range N := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_range]
        have h1 := (Nat.le_floor_iff hx0).1 hn.2
        exact_mod_cast lt_of_le_of_lt h1 hx
      calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)
          = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * max (x / n - 1) 0 := by
            refine Finset.sum_congr rfl fun n hn => ?_
            rw [Finset.mem_Icc] at hn
            have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn.1
            have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 hn.2
            rw [max_eq_left]
            rw [sub_nonneg, le_div_iff₀ (by linarith)]
            linarith
        _ = ∑ n ∈ Finset.range N, Λ n * max (x / n - 1) 0 := by
            refine Finset.sum_subset hsub fun n _ hn => ?_
            rw [Finset.mem_Icc, not_and_or] at hn
            rcases hn with h | h
            · have h0 : n = 0 := by omega
              subst h0
              simp
            · have hxn : x < n := by
                by_contra hc
                push_neg at hc
                exact h ((Nat.le_floor_iff hx0).2 hc)
              have hn0 : (0:ℝ) < n := hx0.trans_lt hxn
              rw [max_eq_right, mul_zero]
              rw [sub_nonpos, div_le_one hn0]
              exact hxn.le
    · push_neg at hx0
      rw [show ⌊x⌋₊ = 0 from Nat.floor_of_nonpos hx0.le]
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      symm
      refine Finset.sum_eq_zero fun n _ => ?_
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have hn0 : (0:ℝ) < n := by exact_mod_cast h
        rw [max_eq_right, mul_zero]
        rw [sub_nonpos, div_le_one hn0]
        have : (1:ℝ) ≤ n := by exact_mod_cast h
        linarith
  have hyN : y < ((⌊y⌋₊ + 2 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one y
    push_cast
    linarith
  have hg : Continuous (fun x : ℝ => ((∑ n ∈ Finset.range (⌊y⌋₊ + 2), Λ n * max (x / n - 1) 0 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_finset_sum _ fun n _ =>
      continuous_const.mul (((continuous_id.div_const _).sub continuous_const).max continuous_const))
  refine hg.continuousAt.congr ?_
  filter_upwards [Iio_mem_nhds hyN] with x hx
  rw [key _ x hx]
end Formalism.ZF
