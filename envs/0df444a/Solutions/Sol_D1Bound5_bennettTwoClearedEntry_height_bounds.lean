-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_height_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:45:51.057426+00:00
-- url     : https://prove2.me/submissions/caabb4ff-2d9d-4735-94ca-7b8a5bc0620b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_one_norm_le_local
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_two_norm_le_local
import Theorems.Thm_D1Bound5_bennett_two_height_normalization

section
namespace D1Bound5

private theorem bennett_norm_add_interval (N z : ℂ) :
    ‖N‖ - ‖z‖ ≤ ‖N + z‖ ∧ ‖N + z‖ ≤ ‖N‖ + ‖z‖ := by
  constructor
  · have h : ‖N‖ ≤ ‖N + z‖ + ‖z‖ := by
      simpa using norm_add_le (N + z) (-z)
    linarith
  · exact norm_add_le _ _

/-- Actual uniform entry bounds at every positive order. The positive-series
proof absorbs its small numerator loss into the paper's rounding to42 and
thus obtains the slightly stronger bounds without the prefactor p2. -/
theorem _root_.solution
    (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1000 ≤ ‖a‖ * ‖c‖)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖bennettTwoClearedEntry a b c k i 1‖ < (42 * ‖a‖ ^ 2 * ‖b‖ * ‖c‖) ^ k ∧
    ‖bennettTwoClearedEntry a b c k i 2‖ < (42 * ‖b‖ ^ 3 * ‖c‖) ^ k := by
  let A := ‖a‖
  let B := ‖b‖
  let C := ‖c‖
  let δ := ‖a - b‖
  let N := A * B * C
  let U1 := ‖a * b * c + b‖
  let U2 := ‖a * b * c + a‖
  let r1 := 2 * min B δ / 5
  let r2 := 2 * min A δ / 5
  have hA : 0 < A := norm_pos_iff.mpr ha
  have hB : 0 < B := norm_pos_iff.mpr hb
  have hC : 0 < C := norm_pos_iff.mpr hc
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hδAB : δ ≤ A + B := norm_sub_le a b
  have hnormN : ‖a * b * c‖ = N := by simp only [norm_mul]; rfl
  have hscale : 1000 ≤ N / B := by
    have heq : N / B = A * C := by dsimp [N]; field_simp [hB.ne']
    rw [heq]
    exact hAC
  have hNgt : B < N := by
    have hs := (le_div_iff₀ hB).mp hscale
    nlinarith
  have hU1 := bennett_norm_add_interval (a * b * c) b
  have hU2 := bennett_norm_add_interval (a * b * c) a
  rw [hnormN] at hU1 hU2
  have hU1lo : N - B ≤ U1 := hU1.1
  have hU1hi : U1 ≤ N + B := hU1.2
  have hU2lo : N - A ≤ U2 := hU2.1
  have hU2hi : U2 ≤ N + A := hU2.2
  have hU1pos : 0 < U1 := by linarith
  have hU2pos : 0 < U2 := by change A ≤ B at hAB; linarith
  have hr1 : 0 < r1 := by dsimp [r1]; exact div_pos (mul_pos (by norm_num) (lt_min hB hδ)) (by norm_num)
  have hr2 : 0 < r2 := by dsimp [r2]; exact div_pos (mul_pos (by norm_num) (lt_min hA hδ)) (by norm_num)
  have hr1B : 2 * r1 ≤ B := by dsimp [r1]; nlinarith [min_le_left B δ, lt_min hB hδ]
  have hr1δ : 2 * r1 ≤ δ := by dsimp [r1]; nlinarith [min_le_right B δ, lt_min hB hδ]
  have hr2A : 2 * r2 ≤ A := by dsimp [r2]; nlinarith [min_le_left A δ, lt_min hA hδ]
  have hr2δ : 2 * r2 ≤ δ := by dsimp [r2]; nlinarith [min_le_right A δ, lt_min hA hδ]
  have hlocal1 := bennettTwoClearedEntry_one_norm_le_local a b c k hk i
    r1 hr1 hU1pos hr1B hr1δ
  have hlocal2 := bennettTwoClearedEntry_two_norm_le_local a b c k hk i
    r2 hr2 hU2pos hr2A hr2δ
  have hnormal1 := bennett_two_height_normalization B A δ B C N U1 r1 k
    hB hA hδ hB hC le_rfl (by change A ≤ B at hAB; linarith)
    (by dsimp [N]; ring) hscale hU1lo hU1hi rfl hk
  have hnormal2 := bennett_two_height_normalization A B δ B C N U2 r2 k
    hA hB hδ hB hC hAB hδAB rfl hscale hU2lo hU2hi rfl hk
  constructor
  · apply hlocal1.trans_lt
    have hswap : 4 * B * A * δ^2 = 4 * A * B * δ^2 := by ring
    rw [hswap] at hnormal1
    exact hnormal1
  · apply hlocal2.trans_lt
    have hcube : 42 * B^2 * B * C = 42 * B^3 * C := by ring
    rw [hcube] at hnormal2
    exact hnormal2

end D1Bound5
end
