-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.count_a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:46.362716+00:00
-- url     : https://prove2.me/submissions/4dcbee1b-dccc-4662-be69-925f336eb461

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_count_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (hP : PNTAPRelW) (hE : Formalism.ZeroFreeDirichlet.ExcBound) (ε : ℝ) (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ (x X : ℝ) (m₀ a₀ : ℕ),
    x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ → a₀.Coprime m₀ →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := by
  obtain ⟨c₃, A₀, C₀, hc₃, hPM⟩ := hP
  obtain ⟨c0, hc0, hcb0⟩ := hE 1 one_pos
  have hcpos : 0 < min c0 1 := lt_min hc0 one_pos
  have hc1 : min c0 1 ≤ 1 := min_le_right _ _
  refine ⟨Real.exp (320 + 4 * |C₀| * (5 + ε / 5) + |4 * Real.log (4 * (|A₀| + 1)) / c₃|
    + |4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃| + |Real.log (320 / min c0 1)|), ?_⟩
  intro x X m₀ a₀ hx hm0 h8 hcop h1 h6 h3
  haveI : NeZero m₀ := ⟨hm0.ne'⟩
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx : 320 + 4 * |C₀| * (5 + ε / 5) + |4 * Real.log (4 * (|A₀| + 1)) / c₃|
      + |4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃| + |Real.log (320 / min c0 1)| ≤ Real.log x := by
    rw [← Real.exp_le_exp, Real.exp_log hxpos]
    exact hx
  have hC0 : 0 ≤ 4 * |C₀| * (5 + ε / 5) := mul_nonneg (by positivity) (by linarith)
  have a1 := abs_nonneg (4 * Real.log (4 * (|A₀| + 1)) / c₃)
  have a2 := abs_nonneg (4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃)
  have a3 := abs_nonneg (Real.log (320 / min c0 1))
  have hl320 : 320 ≤ Real.log x := by linarith
  have hx1 : 1 ≤ x := by
    have h := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hxpos] at h
    linarith
  have hlC : 4 * |C₀| * (5 + ε / 5) ≤ Real.log x := by linarith
  have hlK1 : 4 * Real.log (4 * (|A₀| + 1)) / c₃ ≤ Real.log x := by
    linarith [le_abs_self (4 * Real.log (4 * (|A₀| + 1)) / c₃)]
  have hlK2 : 4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃ ≤ Real.log x := by
    linarith [le_abs_self (4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃)]
  have hlc : |Real.log (320 / min c0 1)| ≤ Real.log x := by linarith
  obtain ⟨e, he1, -, he3⟩ := hPM m₀ h8
  have hcb : ∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), χ ^ 2 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - min c0 1 * (m₀ : ℝ) ^ (-1 : ℝ) := by
    intro χ β h1' h2' h3'
    have h := hcb0 m₀ χ β h1' h2' h3'
    have hpow : 0 ≤ (m₀ : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left c0 1) hpow]
  by_cases hpos : 0 < X
  · exact count_pos hc₃ hcpos hc1 hε h8 a₀ hcop e he1 he3 hcb x X hx1 hl320 hlC hlK1 hlK2 hlc h1 h3 hpos
  · have hXle : X ≤ 0 := not_lt.mp hpos
    rcases hXle.lt_or_eq with hneg | hzero
    · have hcard : (0:ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := Nat.cast_nonneg _
      rw [Real.rpow_def_of_neg hneg]
      have hcos : Real.cos (9 / 10 * Real.pi) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      nlinarith [Real.exp_pos (Real.log X * (9 / 10))]
    · subst hzero
      rw [Real.zero_rpow (by norm_num)]
      exact Nat.cast_nonneg _
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
