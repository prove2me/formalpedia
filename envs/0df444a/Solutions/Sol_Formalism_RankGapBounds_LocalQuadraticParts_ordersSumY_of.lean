-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.ordersSumY_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:31.595652+00:00
-- url     : https://prove2.me/submissions/000adcc1-223a-4e3e-959d-2896aa8db255

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_resid
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_y_sum
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_modulus_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.RankGapBounds.LocalQuadraticParts
open Finset
private theorem div_le_div_of_mul_le_mul_of_pos' {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  first
  | exact (div_le_div_iff_of_pos hb hd).mpr h
  | exact (div_le_div_iff hb hd).mpr h
  | exact (div_le_div_iff₀ hb hd).mpr h
private theorem one_half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  linarith
end Formalism.RankGapBounds.LocalQuadraticParts
end

set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (hI : OrdersIff) : OrdersSumY := by
  refine ⟨12, ?_⟩
  intro e J Y s he hJ hY hs
  obtain ⟨hM2, -, hJM⟩ := pm_modulus_facts e J hJ
  have hY0 : 0 ≤ Y := by linarith
  have hs' : ∀ l ∈ s, 3 ≤ l ∧ l ≤ ⌊Y⌋₊ ∧
      ((l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = 1 ∨
        (l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = -1) := by
    intro l hl
    obtain ⟨hp, h2, hlY, hl', hord⟩ := hs l hl
    have hodd : l % 2 = 1 := hp.eq_two_or_odd.resolve_left h2
    have h3 : 3 ≤ l := by have := hp.two_le; omega
    exact ⟨h3, Nat.le_floor hlY, pm_resid hI e J l hl' hodd hord⟩
  have hsum := pm_y_sum _ ⌊Y⌋₊ hM2 Y hY (Nat.floor_le hY0) s hs'
    (fun l hl => (hs l hl).2.2.1)
  set M : ℕ := 2 ^ (e + 2 - min e (Nat.log 2 J)) with hMdef
  have hm2 : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hm0 : (0 : ℝ) < M := by linarith
  have hP : (2 : ℝ) ^ e ≤ (J : ℝ) * M := by exact_mod_cast hJM
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hL := one_half_le_log_two
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hΛ : Real.log ((2 : ℝ) ^ e * Y) = e * Real.log 2 + Real.log Y := by
    rw [Real.log_mul (by positivity) (show (0 : ℝ) < Y by linarith).ne', Real.log_pow]
  have hΛ1 : 1 / 2 ≤ (e : ℝ) * Real.log 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e - 1) (by linarith : (0 : ℝ) ≤ Real.log 2)]
  have hkey : Real.log Y * (1 + Real.log Y) ≤ 3 * Real.log ((2 : ℝ) ^ e * Y) ^ 2 := by
    rw [hΛ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hΛ1) hlY, sq_nonneg ((e : ℝ) * Real.log 2),
      sq_nonneg (Real.log Y)]
  have hPpos : (0 : ℝ) < 2 ^ e := by positivity
  calc ∑ l ∈ s, Real.log l / (l : ℝ) ≤ 4 * Real.log Y * (1 + Real.log Y) / M := hsum
    _ ≤ 12 * (J : ℝ) * Real.log ((2 : ℝ) ^ e * Y) ^ 2 / (2 : ℝ) ^ e := by
      apply div_le_div_of_mul_le_mul_of_pos' hm0 hPpos
      nlinarith [mul_nonneg (sub_nonneg.mpr hkey) hPpos.le,
        mul_nonneg (sq_nonneg (Real.log ((2 : ℝ) ^ e * Y))) (sub_nonneg.mpr hP)]
end Formalism.RankGapBounds.LocalQuadraticParts
