-- Prove2me | solution 1 for BanditAlgorithm.alloc_settling_of_tracking_and_target_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T20:31:24.7199+00:00
-- url     : https://prove2.me/submissions/ae00fb42-732d-421c-96ce-ea53e6640fec

import Theorems.Thm_BanditAlgorithm_cesaro_average_forgets_transient
import Theorems.Thm_BanditAlgorithm_tsum_weight_of_tail_cover
import Theorems.Thm_BanditAlgorithm_tsum_sq_mean_failure_ne_top_of_forced_exploration
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Tracking a target that follows the estimates makes the allocation settle

The allocation half of Garivier and Kaufmann's Proposition 13, separated from the
rule that realises it.  Nothing below mentions a particular sampling rule: the
hypotheses name a *tracked target* `p ω s`, a probability vector chosen at round
`s` on the trajectory `ω`, and ask only that

* the counts follow its partial sums to within a constant `C` (tracking), and
* the target is within `ξ/2` of the limit `α` from a fixed round `S₀` on, as
  soon as the empirical means are `ε`-accurate (the plug-in map is continuous at
  `μ`, and any exploration floor has worn off).

Both are properties of the rule alone; the probabilistic content is entirely in
the accuracy of the means, which enters through the forced-exploration floor.

The conclusion is the pair the settling argument consumes: the empirical
allocation is eventually within `ξ` of `α` almost surely, and its failure series
converges against the linear weight `n+1`.

The argument is a trade of a moment for a delay.  A Cesàro average forgets its
transient at rate `1/n`, so an allocation failure at round `n` cannot be caused by
anything that happened before round `≍ ξn/4`: it forces a failure of the *means*
at some round `m ≥ ⌈(ξ/4)n⌉`.  Exchanging the two sums, each mean failure at `m`
is then charged for the `O(m)` allocation rounds below it, which turns the weight
`n+1` into `(m+1)²` — and the means' quadratically weighted failure series
converges because the forced-exploration floor makes it sub-exponential.

The almost-sure half is then Borel-Cantelli applied to the same series, so it
needs no separate consistency argument for the estimates.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The two events -/

/-- The allocation is within `ξ` of `α` at round `n` (and the round is positive,
so that the empirical allocation is defined). -/
def allocOK (α : Fin k → ℝ) (ξ : ℝ) (n : ℕ) : Set (ℕ → Fin k × ℝ) :=
  {ω | 0 < n ∧ ∀ i, |trajAllocation i n ω - α i| ≤ ξ}

/-- The empirical means are within `ε` of `μ` at round `m`. -/
def meanOK (μvec : Fin k → ℝ) (ε : ℝ) (m : ℕ) : Set (ℕ → Fin k × ℝ) :=
  {ω | ∀ i, |trajEmpiricalMean i m ω - μvec i| ≤ ε}

/-- `T_i(t)`, as a real-valued statistic of the whole trajectory. -/
theorem measurable_trajPullCount_real (i : Fin k) (t : ℕ) :
    Measurable (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount i t ω : ℕ) : ℝ)) := by
  classical
  have hrw : (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount i t ω : ℕ) : ℝ)) =
      fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ Finset.range t, if (ω s).1 = i then (1 : ℝ) else 0 := by
    funext ω
    rw [trajPullCount, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by split <;> simp
  rw [hrw]
  refine Finset.measurable_sum _ fun s _ ↦ ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_fst.comp (measurable_pi_apply s)) (measurableSet_singleton i)

theorem measurable_trajAllocation_amb (i : Fin k) (t : ℕ) :
    Measurable (trajAllocation i t) := by
  have hrw : trajAllocation i t = fun ω : ℕ → Fin k × ℝ ↦
      ((trajPullCount i t ω : ℕ) : ℝ) / (t : ℝ) := rfl
  rw [hrw]
  exact (measurable_trajPullCount_real i t).div measurable_const

theorem measurableSet_allocOK [NeZero k] (α : Fin k → ℝ) (ξ : ℝ) (n : ℕ) :
    MeasurableSet (allocOK α ξ n) := by
  classical
  by_cases hn : 0 < n
  · have hset : allocOK α ξ n
        = ⋂ i : Fin k, {ω : ℕ → Fin k × ℝ | |trajAllocation i n ω - α i| ≤ ξ} := by
      ext ω
      simp only [allocOK, Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h i ↦ h.2 i, fun h ↦ ⟨hn, h⟩⟩
    rw [hset]
    refine MeasurableSet.iInter fun i ↦ ?_
    have hmeas : Measurable fun ω : ℕ → Fin k × ℝ ↦ |trajAllocation i n ω - α i| :=
      ((measurable_trajAllocation_amb i n).sub measurable_const).abs
    exact measurableSet_le hmeas measurable_const
  · have hset : allocOK α ξ n = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun ω hω ↦ hn hω.1
    rw [hset]
    exact MeasurableSet.empty

/-! ## The round past which the Cesàro estimate closes -/

/-- The transient costs `C + S₀ + 1`, and the Cesàro estimate has `ξ/4` of room
for it, so the cover starts here. -/
noncomputable def settleRound (C : ℝ) (S₀ : ℕ) (ξ : ℝ) : ℕ :=
  ⌈4 * (C + (S₀ : ℝ) + 1) / ξ⌉₊

theorem settleRound_pos {C : ℝ} (hC : 0 ≤ C) (S₀ : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    0 < settleRound C S₀ ξ := by
  refine Nat.ceil_pos.mpr ?_
  have hS : (0 : ℝ) ≤ (S₀ : ℝ) := Nat.cast_nonneg S₀
  positivity

/-! ## The deterministic cover -/

/-- **A late allocation failure forces a late mean failure.**  If the means are
`ε`-accurate from round `J` on, `J` is below `ξn/4 + 1`, and `n` is past
`settleRound`, then the allocation is accurate at `n`. -/
theorem allocOK_of_mean_tail [NeZero k] {μvec α : Fin k → ℝ}
    {p : (ℕ → Fin k × ℝ) → ℕ → Fin k → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    (hp0 : ∀ ω s i, 0 ≤ p ω s i) (hp1 : ∀ ω s i, p ω s i ≤ 1)
    {ξ ε : ℝ} (hξ : 0 < ξ) {S₀ : ℕ} {ω : ℕ → Fin k × ℝ}
    (htrack : ∀ (n : ℕ) (i : Fin k),
      |(trajPullCount i n ω : ℝ) - ∑ s ∈ Finset.range n, p ω s i| ≤ C)
    (hmod : ∀ s : ℕ, S₀ ≤ s →
      (∀ l, |trajEmpiricalMean l s ω - μvec l| ≤ ε) → ∀ j, |p ω s j - α j| ≤ ξ / 2)
    {J n : ℕ} (hJ : ∀ s : ℕ, J ≤ s → ∀ l, |trajEmpiricalMean l s ω - μvec l| ≤ ε)
    (hn : settleRound C S₀ ξ ≤ n) (hJn : (J : ℝ) ≤ ξ * (n : ℝ) / 4 + 1) :
    ω ∈ allocOK α ξ n := by
  classical
  have hnpos : 0 < n := lt_of_lt_of_le (settleRound_pos hC S₀ hξ) hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  set M : ℕ := max J S₀ with hMdef
  refine ⟨hnpos, fun j ↦ ?_⟩
  -- the crude global bound on the target
  have hB : ∀ s : ℕ, |p ω s j - α j| ≤ 1 := by
    intro s
    rw [abs_le]
    exact ⟨by linarith [hp0 ω s j, hα1 j], by linarith [hp1 ω s j, hα0 j]⟩
  -- the tail bound
  have htail : ∀ s : ℕ, M ≤ s → |p ω s j - α j| ≤ ξ / 2 := by
    intro s hs
    exact hmod s (le_trans (le_max_right J S₀) hs)
      (fun l ↦ hJ s (le_trans (le_max_left J S₀) hs) l) j
  -- the Cesàro estimate
  have hces := cesaro_average_forgets_transient
    (p := fun s ↦ p ω s j) (N := fun t ↦ (trajPullCount j t ω : ℝ)) (a := α j)
    (C := C) (B := 1) (δ := ξ / 2) (M := M)
    (fun t ↦ htrack t j) hB (by linarith) htail hnpos
  rw [mul_one] at hces
  -- the transient is small past the threshold
  have hMbound : (M : ℝ) ≤ ξ * (n : ℝ) / 4 + 1 + (S₀ : ℝ) := by
    have hcast : ((max J S₀ : ℕ) : ℝ) = max (J : ℝ) (S₀ : ℝ) := Nat.cast_max _ _
    rw [hMdef, hcast]
    have hS0nn : (0 : ℝ) ≤ (S₀ : ℝ) := Nat.cast_nonneg S₀
    have hξn : (0 : ℝ) ≤ ξ * (n : ℝ) / 4 + 1 := by positivity
    exact max_le (by linarith) (by linarith)
  have hthr : (C + (M : ℝ)) / (n : ℝ) ≤ ξ / 2 := by
    have hnbig : 4 * (C + (S₀ : ℝ) + 1) / ξ ≤ (n : ℝ) := by
      have h1 : ((settleRound C S₀ ξ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      refine le_trans ?_ h1
      unfold settleRound
      exact Nat.le_ceil _
    rw [div_le_iff₀ hnR]
    rw [div_le_iff₀ hξ] at hnbig
    nlinarith [hMbound, hnR, hξ]
  have hfinal : |(trajPullCount j n ω : ℝ) / (n : ℝ) - α j| ≤ ξ := by
    refine le_trans hces ?_
    linarith [hthr]
  have hrw : trajAllocation j n ω = (trajPullCount j n ω : ℝ) / (n : ℝ) := rfl
  rw [hrw]
  exact hfinal

/-! ## The cover, in the exchange lemma's form -/

theorem allocOK_compl_subset_mean_tail [NeZero k] {μvec α : Fin k → ℝ}
    {p : (ℕ → Fin k × ℝ) → ℕ → Fin k → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    (hp0 : ∀ ω s i, 0 ≤ p ω s i) (hp1 : ∀ ω s i, p ω s i ≤ 1)
    {ξ ε : ℝ} (hξ : 0 < ξ) {S₀ : ℕ} {G : Set (ℕ → Fin k × ℝ)}
    (htrack : ∀ ω ∈ G, ∀ (n : ℕ) (i : Fin k),
      |(trajPullCount i n ω : ℝ) - ∑ s ∈ Finset.range n, p ω s i| ≤ C)
    (hmod : ∀ ω ∈ G, ∀ s : ℕ, S₀ ≤ s →
      (∀ l, |trajEmpiricalMean l s ω - μvec l| ≤ ε) → ∀ j, |p ω s j - α j| ≤ ξ / 2)
    {n : ℕ} (hn : settleRound C S₀ ξ ≤ n) :
    (allocOK α ξ n)ᶜ ∩ G
      ⊆ ⋃ m : {m : ℕ // ⌈(ξ / 4) * (n : ℝ)⌉₊ ≤ m}, (meanOK μvec ε (m : ℕ))ᶜ := by
  classical
  rintro ω ⟨hfail, hωG⟩
  by_contra hcon
  set J : ℕ := ⌈(ξ / 4) * (n : ℝ)⌉₊ with hJdef
  have hJ : ∀ s : ℕ, J ≤ s → ∀ l, |trajEmpiricalMean l s ω - μvec l| ≤ ε := by
    intro s hs l
    by_contra hbad
    exact hcon (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, by
      simp only [Set.mem_compl_iff, meanOK, Set.mem_setOf_eq]
      exact fun hall ↦ hbad (hall l)⟩)
  have hJn : (J : ℝ) ≤ ξ * (n : ℝ) / 4 + 1 := by
    rw [hJdef]
    have hnn : (0 : ℝ) ≤ (ξ / 4) * (n : ℝ) := by positivity
    have h := Nat.ceil_lt_add_one (a := (ξ / 4) * (n : ℝ)) hnn
    linarith
  exact hfail (allocOK_of_mean_tail hC hα0 hα1 hp0 hp1 hξ
    (htrack ω hωG) (hmod ω hωG) hJ hn hJn)

/-! ## Borel-Cantelli -/

/-- A summable failure series makes the event hold eventually, almost surely. -/
theorem ae_eventually_of_tsum_compl_ne_top {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {A : ℕ → Set Ω} (hA : ∑' n : ℕ, ν (A n)ᶜ ≠ ⊤) :
    ∀ᵐ ω ∂ν, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ω ∈ A n := by
  have hzero : ν {ω | ∃ᶠ n in atTop, ω ∈ (A n)ᶜ} = 0 :=
    measure_setOf_frequently_eq_zero (p := fun n ω ↦ ω ∈ (A n)ᶜ) hA
  rw [ae_iff]
  refine measure_mono_null (fun ω hω ↦ ?_) hzero
  simp only [Set.mem_setOf_eq, not_exists, not_forall] at hω ⊢
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨n, hn, hmem⟩ := hω N
  exact ⟨n, hn, hmem⟩

end BanditAlgorithm

open BanditAlgorithm

/-- **The allocation half of Proposition 13, for any rule tracking a target that
follows the estimates.** -/
theorem solution {k : ℕ} [NeZero k] (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k)
    (p : (ℕ → Fin k × ℝ) → ℕ → Fin k → ℝ) (α : Fin k → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (G : Set (ℕ → Fin k × ℝ))
    (hG : BanditAlgorithm.banditTrajMeasure
      (BanditAlgorithm.gaussianBandit μvec) pol Gᶜ = 0)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    (hp0 : ∀ ω s i, 0 ≤ p ω s i) (hp1 : ∀ ω s i, p ω s i ≤ 1)
    (htrack : ∀ ω ∈ G, ∀ (n : ℕ) (i : Fin k),
      |(BanditAlgorithm.trajPullCount i n ω : ℝ)
        - ∑ s ∈ Finset.range n, p ω s i| ≤ C)
    (hcount : ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
        (BanditAlgorithm.gaussianBandit μvec) pol),
      ∀ (t : ℕ) (j : Fin k),
        Real.sqrt (t : ℝ) - 2 * (k : ℝ) ≤ (BanditAlgorithm.trajPullCount j t ω : ℝ))
    {ξ : ℝ} (hξ : 0 < ξ) {ε : ℝ} (hε : 0 < ε) {S₀ : ℕ}
    (hmod : ∀ ω ∈ G, ∀ s : ℕ, S₀ ≤ s →
      (∀ l, |BanditAlgorithm.trajEmpiricalMean l s ω - μvec l| ≤ ε) →
      ∀ j, |p ω s j - α j| ≤ ξ / 2) :
    (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
        (BanditAlgorithm.gaussianBandit μvec) pol),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (0 < n ∧ ∀ i, |BanditAlgorithm.trajAllocation i n ω - α i| ≤ ξ))
      ∧ ∑' n : ℕ, ((n : ℝ≥0∞) + 1) *
          BanditAlgorithm.banditTrajMeasure
            (BanditAlgorithm.gaussianBandit μvec) pol
            {ω : ℕ → Fin k × ℝ |
              0 < n ∧ ∀ i, |BanditAlgorithm.trajAllocation i n ω - α i| ≤ ξ}ᶜ ≠ ⊤ := by
  classical
  set P : Measure (ℕ → Fin k × ℝ) :=
    banditTrajMeasure (gaussianBandit μvec) pol with hP
  -- the series, by the exchange lemma
  have hseries : ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * P (allocOK α ξ n)ᶜ ≠ ⊤ := by
    refine tsum_weight_of_tail_cover (B := fun m ↦ meanOK μvec ε m) hG
      (θ := ξ / 4) (by linarith) (N₀ := settleRound C S₀ ξ) ?_ ?_
    · intro n hn
      exact allocOK_compl_subset_mean_tail hC hα0 hα1 hp0 hp1 hξ htrack hmod hn
    · exact tsum_sq_mean_failure_ne_top_of_forced_exploration μvec pol hε hcount
  -- the almost-sure half, by Borel-Cantelli applied to the same series
  have hsummable : ∑' n : ℕ, P (allocOK α ξ n)ᶜ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hseries (ENNReal.tsum_le_tsum fun n ↦ ?_)
    calc P (allocOK α ξ n)ᶜ = 1 * P (allocOK α ξ n)ᶜ := (one_mul _).symm
      _ ≤ ((n : ℝ≥0∞) + 1) * P (allocOK α ξ n)ᶜ := by
          gcongr
          exact le_add_self
  exact ⟨ae_eventually_of_tsum_compl_ne_top hsummable, hseries⟩
