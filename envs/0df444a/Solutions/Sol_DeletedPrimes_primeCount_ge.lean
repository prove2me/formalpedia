-- Prove2me | solution 1 for DeletedPrimes.primeCount_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:17:51.297748+00:00
-- url     : https://prove2.me/submissions/1b880fa6-84f2-4f1f-aba3-1a3c96043f28

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
import Theorems.Thm_DeletedPrimes_mertensSum_sub
import Theorems.Thm_DeletedPrimes_mem_mertens_sdiff
import Theorems.Thm_DeletedPrimes_tendsto_mertens_comp
import Theorems.Thm_DeletedPrimes_tendsto_log_rpow_div

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hM : MertensLaw S α m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, x ^ (α - ε) ≤ primeCount S x := by
  set ε' : ℝ := min (1 / 2) (ε / (2 * α)) with hε'
  have hε'0 : 0 < ε' := lt_min (by norm_num) (by positivity)
  have hε'1 : ε' ≤ 1 / 2 := min_le_left _ _
  have hε'2 : ε' ≤ ε / (2 * α) := min_le_right _ _
  have hαε : α * ε' ≤ ε / 2 := by
    calc α * ε' ≤ α * (ε / (2 * α)) := mul_le_mul_of_nonneg_left hε'2 hα.le
      _ = ε / 2 := by field_simp
  set β : ℝ := α * (1 - ε') with hβ
  have hβgap : 0 < β - (α - ε) := by rw [hβ]; nlinarith
  have hinc : Tendsto (fun x => (mertensSum S α x - mertensSum S α (x ^ (1 - ε'))) / Real.log x)
      atTop (𝓝 (m - m * (1 - ε'))) := by
    have hB := tendsto_mertens_comp hM (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ε'))
      (tendsto_log_rpow_div (1 - ε'))
    exact (hM.sub hB).congr fun x => (sub_div _ _ _).symm
  have hpos : m * ε' / 2 < m - m * (1 - ε') := by nlinarith
  have hpow : Tendsto (fun x : ℝ => x ^ (β - (α - ε))) atTop atTop := tendsto_rpow_atTop hβgap
  filter_upwards [hinc.eventually (lt_mem_nhds hpos), hpow.eventually_ge_atTop (2 / (m * ε')),
    eventually_gt_atTop 1] with x hx1 hx2 hx3
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx3
  have hle : x ^ (1 - ε') ≤ x := by
    calc x ^ (1 - ε') ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx3.le (by linarith)
      _ = x := Real.rpow_one x
  set D := (Finset.Icc 1 ⌊x⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊x ^ (1 - ε')⌋₊).filter (· ∈ S)
    with hD
  have hlow : m * ε' / 2 * Real.log x < mertensSum S α x - mertensSum S α (x ^ (1 - ε')) := by
    rwa [lt_div_iff₀ hlog] at hx1
  have hxβ : 0 < x ^ β := by positivity
  have hup : mertensSum S α x - mertensSum S α (x ^ (1 - ε')) ≤
      (D.card : ℝ) * (Real.log x / x ^ β) := by
    rw [mertensSum_sub S α hle, ← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    obtain ⟨-, hp1, hp2, hp3⟩ := mem_mertens_sdiff (by positivity) hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    apply div_le_div₀ hlog.le (Real.log_le_log hp0 hp3) hxβ
    calc x ^ β = (x ^ (1 - ε')) ^ α := by rw [← Real.rpow_mul hx0.le, mul_comm]
      _ ≤ (p : ℝ) ^ α := Real.rpow_le_rpow (by positivity) hp2.le hα.le
  have hcard : m * ε' / 2 * x ^ β ≤ D.card := by
    have h1 : m * ε' / 2 * Real.log x < D.card * (Real.log x / x ^ β) := hlow.trans_le hup
    have h2 : (m * ε' / 2 * x ^ β) * Real.log x < D.card * Real.log x := by
      have := mul_lt_mul_of_pos_right h1 hxβ
      calc (m * ε' / 2 * x ^ β) * Real.log x = m * ε' / 2 * Real.log x * x ^ β := by ring
        _ < D.card * (Real.log x / x ^ β) * x ^ β := this
        _ = D.card * Real.log x := by field_simp
    exact (lt_of_mul_lt_mul_right h2 hlog.le).le
  have hsplit : x ^ β = x ^ (β - (α - ε)) * x ^ (α - ε) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hmain : x ^ (α - ε) ≤ m * ε' / 2 * x ^ β := by
    rw [hsplit]
    have hxa : 0 < x ^ (α - ε) := by positivity
    have : 1 ≤ m * ε' / 2 * x ^ (β - (α - ε)) := by
      rw [div_le_iff₀ (by positivity)] at hx2
      nlinarith
    nlinarith
  have hDle : D.card ≤ primeCount S x := by
    unfold primeCount
    exact Finset.card_le_card Finset.sdiff_subset
  calc x ^ (α - ε) ≤ m * ε' / 2 * x ^ β := hmain
    _ ≤ D.card := hcard
    _ ≤ primeCount S x := by exact_mod_cast hDle
end DeletedPrimes
