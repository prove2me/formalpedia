-- Prove2me | solution 1 for FirstPassageLinearTransport.naturalDensityOne_assembleDyadic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:44.534385+00:00
-- url     : https://prove2.me/submissions/4ab64027-1caa-4840-ad21-14a2ccf3c90b

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Theorems.Thm_FirstPassageLinearTransport_shellBad_assembleDyadic
import Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_nonneg
import Theorems.Thm_FirstPassageLinearTransport_shellBad_card_eq_ratio_mul
import Theorems.Thm_FirstPassageLinearTransport_sum_two_pow_range
import Theorems.Thm_FirstPassageLinearTransport_badCount_le_shell_sum
import Theorems.Thm_FirstPassageLinearTransport_card_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (S : ℕ → Set ℕ)
    (hvanish :
      Filter.Tendsto
        (fun M => shellExceptionalRatio (S M) M)
        Filter.atTop (nhds 0)) :
    NaturalDensityOne (assembleDyadic S) := by
  classical
  rw [NaturalDensityOne, Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨M₀, hM₀⟩ :=
    (Metric.tendsto_atTop.1 hvanish) (eps / 8) (by linarith)
  let threshold : ℝ :=
    max ((2 : ℝ) ^ M₀) (8 * (2 : ℝ) ^ M₀ / eps)
  obtain ⟨N₀ : ℕ, hN₀⟩ := exists_nat_gt threshold
  refine ⟨N₀, ?_⟩
  intro N hN
  have hNpos : 0 < N := by
    have hthreshold0 : 0 ≤ threshold := by
      dsimp [threshold]
      positivity
    have hN₀pos : 0 < N₀ := by
      exact_mod_cast lt_of_le_of_lt hthreshold0 hN₀
    omega
  have hNR : threshold < (N : ℝ) := by
    have hN₀R : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    exact hN₀.trans_le hN₀R
  have hNlarge : (2 : ℝ) ^ M₀ < N := by
    change max ((2 : ℝ) ^ M₀) (8 * (2 : ℝ) ^ M₀ / eps) < N at hNR
    exact (le_max_left _ _).trans_lt hNR
  have hNerror : 8 * (2 : ℝ) ^ M₀ / eps < N := by
    change max ((2 : ℝ) ^ M₀) (8 * (2 : ℝ) ^ M₀ / eps) < N at hNR
    exact (le_max_right _ _).trans_lt hNR
  let L := Nat.log 2 N
  have hM₀L : M₀ ≤ L + 1 := by
    by_contra h
    have hLM : L + 1 ≤ M₀ := by omega
    have hpowLe : (2 : ℕ) ^ (L + 1) ≤ 2 ^ M₀ :=
      Nat.pow_le_pow_right (by norm_num) hLM
    have hNlt : N < 2 ^ (L + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) N
    have hNRle : (N : ℝ) < (2 : ℝ) ^ M₀ := by
      exact_mod_cast hNlt.trans_le hpowLe
    linarith
  have hprefix := badCount_le_shell_sum (assembleDyadic S) N
  have hprefixR :
      (badCount (assembleDyadic S) N : ℝ) ≤
        ∑ M ∈ Finset.range (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) := by
    dsimp [L]
    exact_mod_cast hprefix
  rw [← Finset.sum_range_add_sum_Ico
    (fun M => ((shellBad (assembleDyadic S) M).card : ℝ)) hM₀L] at hprefixR
  have hearly :
      ∑ M ∈ Finset.range M₀,
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (2 : ℝ) ^ M₀ := by
    calc
      ∑ M ∈ Finset.range M₀,
          ((shellBad (assembleDyadic S) M).card : ℝ)
          ≤ ∑ M ∈ Finset.range M₀, (2 : ℝ) ^ M := by
            apply Finset.sum_le_sum
            intro M hMr
            have hcard :
                (shellBad (assembleDyadic S) M).card ≤ 2 ^ M := by
              calc
                (shellBad (assembleDyadic S) M).card
                    ≤ (dyadicShell M).card := by
                      apply Finset.card_le_card
                      intro x hx
                      exact (Finset.mem_filter.mp hx).1
                _ = 2 ^ M := card_dyadicShell M
            exact_mod_cast hcard
      _ = (2 : ℝ) ^ M₀ - 1 := sum_two_pow_range M₀
      _ ≤ (2 : ℝ) ^ M₀ := by linarith
  have hlate :
      ∑ M ∈ Finset.Ico M₀ (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (eps / 8) * ((2 : ℝ) ^ (L + 1)) := by
    calc
      ∑ M ∈ Finset.Ico M₀ (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ)
          ≤ ∑ M ∈ Finset.Ico M₀ (L + 1),
              (eps / 8) * (2 : ℝ) ^ M := by
            apply Finset.sum_le_sum
            intro M hM
            rw [shellBad_assembleDyadic, shellBad_card_eq_ratio_mul]
            have hratioAbs := hM₀ M (Finset.mem_Ico.mp hM).1
            rw [Real.dist_eq] at hratioAbs
            have hratio :
                shellExceptionalRatio (S M) M < eps / 8 := by
              have hnonneg := shellExceptionalRatio_nonneg (S M) M
              simpa [abs_of_nonneg hnonneg] using hratioAbs
            exact mul_le_mul_of_nonneg_right hratio.le (by positivity)
      _ ≤ (eps / 8) *
          (∑ M ∈ Finset.range (L + 1), (2 : ℝ) ^ M) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              exact Finset.mem_range.2 (Finset.mem_Ico.mp hx).2
            · intro i _ _
              positivity
      _ = (eps / 8) * ((2 : ℝ) ^ (L + 1) - 1) := by
            rw [sum_two_pow_range]
      _ ≤ (eps / 8) * ((2 : ℝ) ^ (L + 1)) := by
            have hpow0 : 0 ≤ (2 : ℝ) ^ (L + 1) := by positivity
            nlinarith
  have hpowN : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by
    have hpowL : (2 : ℕ) ^ L ≤ N :=
      Nat.pow_log_le_self 2 hNpos.ne'
    rw [pow_succ]
    have hcast : (2 : ℝ) * (2 : ℝ) ^ L ≤ 2 * N := by
      exact_mod_cast Nat.mul_le_mul_left 2 hpowL
    nlinarith
  have hbad :
      (badCount (assembleDyadic S) N : ℝ) ≤
        (2 : ℝ) ^ M₀ + eps * N / 4 := by
    calc
      (badCount (assembleDyadic S) N : ℝ)
          ≤ (∑ M ∈ Finset.range M₀,
              ((shellBad (assembleDyadic S) M).card : ℝ)) +
            ∑ M ∈ Finset.Ico M₀ (L + 1),
              ((shellBad (assembleDyadic S) M).card : ℝ) := hprefixR
      _ ≤ (2 : ℝ) ^ M₀ + (eps / 8) * (2 : ℝ) ^ (L + 1) :=
        add_le_add hearly hlate
      _ ≤ (2 : ℝ) ^ M₀ + eps * N / 4 := by
        nlinarith
  have hearlySmall : (2 : ℝ) ^ M₀ < eps * N / 8 := by
    have heps0 : 0 < eps := heps
    rw [div_lt_iff₀ heps0] at hNerror
    nlinarith
  have hratio :
      (badCount (assembleDyadic S) N : ℝ) / N < eps := by
    have hNR0 : (0 : ℝ) < N := by exact_mod_cast hNpos
    rw [div_lt_iff₀ hNR0]
    nlinarith
  have hratio0 :
      0 ≤ (badCount (assembleDyadic S) N : ℝ) / N := by
    positivity
  simpa [Real.dist_eq, abs_of_nonneg hratio0] using hratio
end FirstPassageLinearTransport
