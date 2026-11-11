-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise46_finite_dyadic_mark_endpoint_weighted_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:46:49.024215+00:00
-- url     : https://prove2.me/submissions/1b3e0eb3-b7d2-492f-8690-e62e6c156676

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise34_dyadic_mark_cell_endpoint_error
import Theorems.Thm_AvramDividend_Classical_avram_anoise43_unit_dyadic_halfopen_cover
import Theorems.Thm_ja18_anoise46_direct_copy_disj_ff94d009
import Theorems.Thm_ja18_anoise46_direct_copy_finite_geometric_sum_bc28acbe
import Theorems.Thm_ja18_anoise46_direct_copy_pointwise_upper_bound_f213822f
import Theorems.Thm_ja18_anoise46_direct_copy_pointwise_upper_bound_ba6b668c
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Finite physical mark collections admit uniformly accurate dyadic signed sums. -/
theorem solution
    {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset α)
    (j : α → ℝ)
    (hF : ∀ u ∈ F, j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) :
    Tendsto
      (fun k : ℕ => ∑ i ∈ Finset.range (2 ^ k),
        (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
          ((F.filter (fun u => j u ∈
            (Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))) ∩
              Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
                (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)))).card : ℝ))
      atTop (𝓝 (∑ u ∈ F, j u)) := by
  classical
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let C : ℕ → ℕ → Set ℝ := fun k i =>
    B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
      (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
  let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k
  let q : ℕ → ℝ := fun k =>
    ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)
  let I : ℝ := ∑ u ∈ F, j u
  let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * (F.card : ℝ)
  have hDisj : (∀ (k i l : ℕ) (hil : i ≠ l), Disjoint (C k i) (C k l)) := ja18_anoise46_direct_copy_disj_ff94d009 (α := α) (n := n) (F := F) (j := j) (hF := hF)
  have hUnique (k : ℕ) (u : α) (hu : u ∈ F) :
      ∃ i : ℕ, i < 2 ^ k ∧ j u ∈ C k i ∧
        ∀ l : ℕ, l < 2 ^ k → j u ∈ C k l → l = i := by
    have huB : j u ∈ B := hF u hu
    have hu0 : j u ≤ 0 := by
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact le_trans huB.2 (le_of_lt (neg_lt_zero.mpr hp))
    obtain ⟨i, hi, hCell⟩ :=
      avram_anoise43_unit_dyadic_halfopen_cover k (j u) huB.1 hu0
    refine ⟨i, hi, ⟨huB, hCell⟩, ?_⟩
    intro l hl hCl
    by_contra hne
    have hdis := hDisj k l i hne
    exact (Set.disjoint_left.mp hdis) hCl ⟨huB, hCell⟩
  have hCountAsSum (k i : ℕ) :
      ((F.filter (fun u => j u ∈ C k i)).card : ℝ) =
        ∑ u ∈ F, if j u ∈ C k i then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  have hReindex : (∀ (k : ℕ), q k =
      ∑ u ∈ F, ∑ i ∈ Finset.range (2 ^ k),
        if j u ∈ C k i then w k i else 0) := ja18_anoise46_direct_copy_finite_geometric_sum_bc28acbe (α := α) (n := n) (F := F) (j := j) (hF := hF) (hDisj := hDisj) (hUnique := hUnique) (hCountAsSum := hCountAsSum)
  have hInner : (∀ (k : ℕ) (u : α) (hu : u ∈ F), |(∑ i ∈ Finset.range (2 ^ k),
          if j u ∈ C k i then w k i else 0) - j u| ≤
        (1 / 2 : ℝ) ^ k) := ja18_anoise46_direct_copy_pointwise_upper_bound_f213822f (α := α) (n := n) (F := F) (j := j) (hF := hF) (hDisj := hDisj) (hUnique := hUnique) (hCountAsSum := hCountAsSum) (hReindex := hReindex)
  have hq : (∀ (k : ℕ), |q k - I| ≤ e k) := ja18_anoise46_direct_copy_pointwise_upper_bound_ba6b668c (α := α) (n := n) (F := F) (j := j) (hF := hF) (hDisj := hDisj) (hUnique := hUnique) (hCountAsSum := hCountAsSum) (hReindex := hReindex) (hInner := hInner)
  have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using hpow.mul_const (F.card : ℝ)
  have hlo : Tendsto (fun k => I - e k) atTop (𝓝 I) := by
    convert tendsto_const_nhds.sub he using 1 <;> simp
  have hhi : Tendsto (fun k => I + e k) atTop (𝓝 I) := by
    convert tendsto_const_nhds.add he using 1 <;> simp
  have hqLimit : Tendsto q atTop (𝓝 I) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    · intro k; linarith [(abs_le.mp (hq k)).1]
    · intro k; linarith [(abs_le.mp (hq k)).2]
  simpa only [q, I, C, B, w] using hqLimit
