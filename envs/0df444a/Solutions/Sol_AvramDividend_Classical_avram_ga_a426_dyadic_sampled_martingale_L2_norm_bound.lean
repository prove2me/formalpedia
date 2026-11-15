-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a426_dyadic_sampled_martingale_L2_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:11:35.302981+00:00
-- url     : https://prove2.me/submissions/47ef8f17-2daa-4edb-979b-773901b81a8d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ) (hMart : Martingale M 𝓕 P)
    (T : ℝ≥0) (k : ℕ) :
    eLpNorm (fun ω => (Finset.range (2^k + 1)).sup'
      (by simp) (fun i => |M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω|)) 2 P
      ≤ 2 * eLpNorm (M T) 2 P := by
  classical
  let N : ℕ := 2 ^ k
  let g : ℕ → ℝ≥0 := fun i => (min i N : ℕ) * T / (N : ℝ≥0)
  have hg : Monotone g := by
    intro i j hij
    dsimp [g]
    gcongr
  have hN : (N : ℝ≥0) ≠ 0 := by
    exact_mod_cast (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0))
  have hgend : g N = T := by
    simp [g, hN]
  let G : Filtration ℕ mΩ := ⟨fun i => 𝓕 (g i),
    fun i j hij => 𝓕.mono (hg hij), fun i => 𝓕.le (g i)⟩
  have hsamp : Martingale (fun i => M (g i)) G P :=
    ⟨fun i => hMart.1 (g i), fun i j hij => hMart.2 (g i) (g j) (hg hij)⟩
  have hdoob := avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal hsamp
    (by norm_num : (1 : ℝ) < 2) N
  have hp : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hc : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = (2 : ℝ≥0∞) := by norm_num
  rw [hp, hc, hgend] at hdoob
  have hgrid (i : ℕ) (hi : i ∈ Finset.range (N + 1)) :
      g i = (i : ℝ≥0) * T / (N : ℝ≥0) := by
    have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    change (((min i N : ℕ) : ℝ≥0) * T / (N : ℝ≥0)) = _
    rw [Nat.min_eq_left hiN]
  have heq : (fun ω => (Finset.range (N + 1)).sup'
      Finset.nonempty_range_add_one (fun i => ‖M (g i) ω‖))
      = (fun ω => (Finset.range (N + 1)).sup'
      Finset.nonempty_range_add_one
        (fun i => |M ((i : ℝ≥0) * T / (N : ℝ≥0)) ω|)) := by
    funext ω
    refine Finset.sup'_congr Finset.nonempty_range_add_one rfl ?_
    intro i hi
    rw [hgrid i hi]
    exact Real.norm_eq_abs _
  rw [heq] at hdoob
  simpa [N] using hdoob
