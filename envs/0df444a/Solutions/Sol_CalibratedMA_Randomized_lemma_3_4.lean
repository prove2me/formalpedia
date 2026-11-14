-- Prove2me | solution 1 for CalibratedMA.Randomized.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Aaron
-- created : 2026-11-13T18:23:51.602108+00:00
-- url     : https://prove2.me/submissions/c0bdbdfa-6113-4af6-9ec5-2bb07528afa7

import Definitions.Def_CalibratedMA_Randomized_Algorithm1
import Theorems.Thm_CalibratedMA_Randomized_lemma_3_3



open MeasureTheory

namespace CalibratedMA.Randomized.GreedyStructure

/-- Each greedy step advances to a grid index no larger than the final endpoint. -/
lemma greedyNext_bounds (ν : Measure ℝ) (K : ℕ) (τ : ℝ) (i : ℕ) (hi : i < K) :
    i < greedyNext ν K τ i ∧ greedyNext ν K τ i ≤ K := by
  classical
  unfold greedyNext
  dsimp only
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    exact Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1
  · exact ⟨hi, le_rfl⟩

/-- The greedy construction never leaves the finite grid. -/
lemma greedyIdx_le (ν : Measure ℝ) (m : ℝ) (K j : ℕ) :
    greedyIdx ν m K j ≤ K := by
  induction j with
  | zero => simp [greedyIdx]
  | succ j ih =>
      rw [greedyIdx]
      split_ifs with h
      · exact (greedyNext_bounds ν K (1 / (64 * m ^ 2)) _ h).2
      · exact le_rfl

/-- Every step before reaching the endpoint strictly increases the grid index. -/
lemma greedyIdx_lt_succ (ν : Measure ℝ) (m : ℝ) (K j : ℕ)
    (hj : greedyIdx ν m K j < K) :
    greedyIdx ν m K j < greedyIdx ν m K (j + 1) := by
  rw [greedyIdx, if_pos hj]
  exact (greedyNext_bounds ν K (1 / (64 * m ^ 2)) _ hj).1

/-- Once the endpoint is reached, all later indices remain there. -/
lemma greedyIdx_stays (ν : Measure ℝ) (m : ℝ) (K j : ℕ)
    (hj : greedyIdx ν m K j = K) (r : ℕ) :
    greedyIdx ν m K (j + r) = K := by
  induction r with
  | zero => simpa using hj
  | succ r ih =>
      change greedyIdx ν m K ((j + r) + 1) = K
      rw [greedyIdx, ih]
      simp only [lt_self_iff_false, if_false]

lemma greedyIdx_eq_K_of_le (ν : Measure ℝ) (m : ℝ) (K i j : ℕ)
    (hi : greedyIdx ν m K i = K) (hij : i ≤ j) :
    greedyIdx ν m K j = K := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact greedyIdx_stays ν m K i hi r

/-- Before stopping, at least one new grid index is traversed per step. -/
lemma step_le_greedyIdx_of_lt (ν : Measure ℝ) (m : ℝ) (K j : ℕ)
    (hj : greedyIdx ν m K j < K) : j ≤ greedyIdx ν m K j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
      by_cases hprev : greedyIdx ν m K j < K
      · have hg := greedyIdx_lt_succ ν m K j hprev
        have hind := ih hprev
        omega
      · have heq : greedyIdx ν m K (j + 1) = K := by
          simp only [greedyIdx, hprev, if_false]
        omega

/-- The endpoint is reached within `K` steps. -/
lemma greedyIdx_hit_K (ν : Measure ℝ) (m : ℝ) (K : ℕ) :
    greedyIdx ν m K K = K := by
  have hle := greedyIdx_le ν m K K
  by_contra hne
  have hlt : greedyIdx ν m K K < K := by omega
  have hge := step_le_greedyIdx_of_lt ν m K K hlt
  omega

/-- The counted interval number is exactly the first index at which the endpoint is reached. -/
lemma greedyNumIntervals_spec (ν : Measure ℝ) (m : ℝ) (K : ℕ) :
    greedyNumIntervals ν m K ≤ K ∧
      greedyIdx ν m K (greedyNumIntervals ν m K) = K ∧
      ∀ j : ℕ, greedyIdx ν m K j < K ↔ j < greedyNumIntervals ν m K := by
  classical
  have hex : ∃ j : ℕ, greedyIdx ν m K j = K := ⟨K, greedyIdx_hit_K ν m K⟩
  let N := Nat.find hex
  have hN : greedyIdx ν m K N = K := Nat.find_spec hex
  have hNK : N ≤ K := Nat.find_min' hex (greedyIdx_hit_K ν m K)
  have hbefore : ∀ j < N, greedyIdx ν m K j < K := by
    intro j hj
    have hle := greedyIdx_le ν m K j
    by_contra hnlt
    have heq : greedyIdx ν m K j = K := by omega
    have hmin : N ≤ j := Nat.find_min' hex heq
    omega
  have hafter : ∀ j, N ≤ j → greedyIdx ν m K j = K := by
    intro j hj
    exact greedyIdx_eq_K_of_le ν m K N j hN hj
  have hiff : ∀ j, greedyIdx ν m K j < K ↔ j < N := by
    intro j
    constructor
    · intro hj
      by_contra hn
      have heq := hafter j (by omega)
      omega
    · exact hbefore j
  have hset : ((Finset.range (K + 1)).filter (fun j => greedyIdx ν m K j < K)) =
      Finset.range N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, hiff]
    omega
  have hnum : greedyNumIntervals ν m K = N := by
    unfold greedyNumIntervals
    rw [hset, Finset.card_range]
  rw [hnum]
  exact ⟨hNK, hN, hiff⟩

lemma greedyNumIntervals_pos (ν : Measure ℝ) (m : ℝ) (K : ℕ) (hK : 1 ≤ K) :
    0 < greedyNumIntervals ν m K := by
  apply (greedyNumIntervals_spec ν m K).2.2 0 |>.mp
  change 0 < K
  omega

/-- Normalizing the strictly increasing greedy indices gives a valid grid partition. -/
lemma greedyPartition_isGridPartition (ν : Measure ℝ) (m : ℝ) (K : ℕ) (hK : 1 ≤ K) :
    IsGridPartition K (greedyPartition ν m K).1 (greedyPartition ν m K).2 := by
  obtain ⟨hMK, hhit, hbefore⟩ := greedyNumIntervals_spec ν m K
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  change IsGridPartition K (greedyNumIntervals ν m K)
    (fun j => (greedyIdx ν m K j : ℝ) / K)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [greedyIdx]
  · dsimp only
    rw [hhit]
    exact div_self (ne_of_gt hKreal)
  · intro j hj
    apply (div_lt_div_iff_of_pos_right hKreal).2
    exact_mod_cast greedyIdx_lt_succ ν m K j ((hbefore j).mpr hj)
  · intro j hj
    exact ⟨greedyIdx ν m K j, greedyIdx_le ν m K j, rfl⟩

end CalibratedMA.Randomized.GreedyStructure


open MeasureTheory

namespace CalibratedMA.Randomized.GreedyContribution

noncomputable def kernel (a b s : ℝ) : ℝ :=
  if a < s ∧ s < b then (s - a) * (b - s) / (b - a) else 0

lemma contribution_eq_integral (ν : Measure ℝ) (a b : ℝ) :
    contribution ν a b = ∫ s, kernel a b s ∂ν := rfl

lemma qj_eq_contribution (ν : Measure ℝ) (γ : ℕ → ℝ) (j : ℕ) :
    qj ν γ j = contribution ν (γ j) (γ (j + 1)) := rfl

lemma kernel_nonneg (a b s : ℝ) : 0 ≤ kernel a b s := by
  unfold kernel
  split_ifs with hs
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr hs.1.le) (sub_nonneg.mpr hs.2.le))
      (sub_nonneg.mpr (hs.1.trans hs.2).le)
  · exact le_refl 0

lemma measurable_kernel (a b : ℝ) : Measurable (kernel a b) := by
  unfold kernel
  apply Measurable.ite (show MeasurableSet (Set.Ioo a b) from measurableSet_Ioo)
  · fun_prop
  · exact measurable_const

lemma kernel_le_quarter_indicator (a b s : ℝ) :
    kernel a b s ≤ (Set.Ioo a b).indicator (fun _ => (b - a) / 4) s := by
  by_cases hs : s ∈ Set.Ioo a b
  · rw [Set.indicator_of_mem hs]
    simp only [kernel, hs.1, hs.2, and_self, ↓reduceIte]
    apply (div_le_iff₀ (sub_pos.mpr (hs.1.trans hs.2))).2
    nlinarith [sq_nonneg (2 * s - a - b)]
  · rw [Set.indicator_of_notMem hs]
    simp [kernel, show ¬(a < s ∧ s < b) from hs]

lemma integrable_kernel (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) :
    Integrable (kernel a b) ν := by
  apply ((integrable_const ((b - a) / 4)).indicator measurableSet_Ioo).mono_nonneg
    (measurable_kernel a b).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (kernel_nonneg a b)
  · exact Filter.Eventually.of_forall (kernel_le_quarter_indicator a b)

lemma contribution_nonneg (ν : Measure ℝ) (a b : ℝ) : 0 ≤ contribution ν a b :=
  integral_nonneg (kernel_nonneg a b)

lemma kernel_self (a s : ℝ) : kernel a a s = 0 := by
  simp only [kernel]
  split_ifs with hs
  · exact False.elim ((lt_asymm hs.1 hs.2))
  · rfl

lemma contribution_self (ν : Measure ℝ) (a : ℝ) : contribution ν a a = 0 := by
  simp only [contribution_eq_integral, kernel_self, integral_zero]

lemma contribution_le_quarter (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) :
    contribution ν a b ≤ (b - a) / 4 * ν.real (Set.Ioo a b) := by
  calc
    contribution ν a b ≤ ∫ s, (Set.Ioo a b).indicator (fun _ => (b - a) / 4) s ∂ν :=
      integral_mono (integrable_kernel ν a b)
        ((integrable_const ((b - a) / 4)).indicator measurableSet_Ioo)
        (kernel_le_quarter_indicator a b)
    _ = _ := by rw [integral_indicator_const _ measurableSet_Ioo, smul_eq_mul, mul_comm]

lemma kernel_overshoot (a b c : ℝ) (_hab : a ≤ b) (hbc : b ≤ c) (s : ℝ) :
    kernel a c s ≤ kernel a b s +
      (Set.Ioo a c).indicator (fun _ => c - b) s := by
  by_cases hs : s ∈ Set.Ioo a c
  · rw [Set.indicator_of_mem hs]
    have hac : 0 < c - a := sub_pos.mpr (hs.1.trans hs.2)
    by_cases hsb : s < b
    · have hab' : 0 < b - a := sub_pos.mpr (hs.1.trans hsb)
      have hrat : (s - a) ^ 2 / ((c - a) * (b - a)) ≤ 1 := by
        apply (div_le_one (mul_pos hac hab')).2
        rw [pow_two]
        exact mul_le_mul (sub_le_sub_right hs.2.le a) (sub_le_sub_right hsb.le a)
          (sub_nonneg.mpr hs.1.le) hac.le
      have heq : kernel a c s = kernel a b s +
          (c - b) * ((s - a) ^ 2 / ((c - a) * (b - a))) := by
        simp only [kernel, hs.1, hs.2, hsb, and_self, ↓reduceIte]
        field_simp
        ring
      rw [heq]
      exact add_le_add (le_refl _) (mul_le_of_le_one_right (sub_nonneg.mpr hbc) hrat)
    · have hbs : b ≤ s := le_of_not_gt hsb
      have hsmall : kernel a c s ≤ c - s := by
        simp only [kernel, hs.1, hs.2, and_self, ↓reduceIte]
        apply (div_le_iff₀ hac).2
        nlinarith [sq_nonneg (c - s)]
      have hold : kernel a b s = 0 := by simp [kernel, hsb]
      rw [hold, zero_add]
      exact hsmall.trans (sub_le_sub_left hbs c)
  · have hnew : kernel a c s = 0 := by simp [kernel, show ¬(a < s ∧ s < c) from hs]
    rw [hnew, Set.indicator_of_notMem hs, add_zero]
    exact kernel_nonneg a b s

lemma contribution_overshoot (ν : Measure ℝ) [IsFiniteMeasure ν] (a b c : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    contribution ν a c ≤ contribution ν a b + (c - b) * ν.real (Set.Ioo a c) := by
  calc
    contribution ν a c ≤
        ∫ s, kernel a b s + (Set.Ioo a c).indicator (fun _ => c - b) s ∂ν :=
      integral_mono (integrable_kernel ν a c)
        ((integrable_kernel ν a b).add
          ((integrable_const (c - b)).indicator measurableSet_Ioo))
        (kernel_overshoot a b c hab hbc)
    _ = _ := by
      rw [integral_add (integrable_kernel ν a b)
        ((integrable_const (c - b)).indicator measurableSet_Ioo)]
      rw [integral_indicator_const _ measurableSet_Ioo, smul_eq_mul]
      rw [contribution_eq_integral, mul_comm]

end CalibratedMA.Randomized.GreedyContribution


open MeasureTheory

namespace CalibratedMA.Randomized.GreedyThreshold

lemma contribution_self (ν : Measure ℝ) (a : ℝ) : contribution ν a a = 0 := by
  simp [contribution]

lemma greedyNext_full_of_lt (ν : Measure ℝ) (K : ℕ) (τ : ℝ) (i : ℕ)
    (hnext : greedyNext ν K τ i < K) :
    τ ≤ contribution ν ((i : ℝ) / K) ((greedyNext ν K τ i : ℝ) / K) := by
  classical
  unfold greedyNext at hnext ⊢
  dsimp only at hnext ⊢
  split_ifs at * with hC
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hC)).2
  · exact (Nat.lt_irrefl K hnext).elim

lemma contribution_lt_before_next (ν : Measure ℝ) (K : ℕ) (τ : ℝ) (i k : ℕ)
    (hik : i < k) (hkK : k ≤ K) (hk : k < greedyNext ν K τ i) :
    contribution ν ((i : ℝ) / K) ((k : ℝ) / K) < τ := by
  classical
  by_contra h
  have hc : k ∈ (Finset.Ioc i K).filter
      (fun k : ℕ => τ ≤ contribution ν ((i : ℝ) / K) ((k : ℝ) / K)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hik, hkK⟩, le_of_not_gt h⟩
  have hC : ((Finset.Ioc i K).filter
      (fun k : ℕ => τ ≤ contribution ν ((i : ℝ) / K) ((k : ℝ) / K))).Nonempty := ⟨k, hc⟩
  unfold greedyNext at hk
  dsimp only at hk
  rw [dif_pos hC] at hk
  exact (not_lt_of_ge (Finset.min'_le _ _ hc)) hk

lemma greedyNext_contribution_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    (K : ℕ) (τ : ℝ) (hτ : 0 < τ) (i : ℕ) (hi : i < K) :
    contribution ν ((i : ℝ) / K) ((greedyNext ν K τ i : ℝ) / K) ≤
      τ + (1 / K) * ν.real (Set.Ioo ((i : ℝ) / K)
        ((greedyNext ν K τ i : ℝ) / K)) := by
  let k := greedyNext ν K τ i
  obtain ⟨hik, hkK⟩ := GreedyStructure.greedyNext_bounds ν K τ i hi
  change i < k at hik
  change k ≤ K at hkK
  have hkpos : 0 < k := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hipred : i ≤ k - 1 := by omega
  have hprev : contribution ν ((i : ℝ) / K) (((k - 1 : ℕ) : ℝ) / K) < τ := by
    rcases hipred.eq_or_lt with heq | hlt
    · rw [← heq, contribution_self]
      exact hτ
    · exact contribution_lt_before_next ν K τ i (k - 1) hlt (by omega) (by change k - 1 < k; omega)
  have hstep : (k : ℝ) / K - ((k - 1 : ℕ) : ℝ) / K = 1 / K := by
    rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
    ring
  have hupper := GreedyContribution.contribution_overshoot ν ((i : ℝ) / K)
    (((k - 1 : ℕ) : ℝ) / K) ((k : ℝ) / K)
    (div_le_div_of_nonneg_right (by exact_mod_cast hipred) hKpos.le)
    (div_le_div_of_nonneg_right (by exact_mod_cast (show k - 1 ≤ k by omega)) hKpos.le)
  rw [hstep] at hupper
  exact hupper.trans (by dsimp only [k] at hprev ⊢; linarith [hprev])

lemma greedy_intervals_full (ν : Measure ℝ) (m : ℝ) (K j : ℕ)
    (hj : j < greedyNumIntervals ν m K - 1) :
    1 / (64 * m ^ 2) ≤ qj ν (greedyPartition ν m K).2 j := by
  have hbefore := (GreedyStructure.greedyNumIntervals_spec ν m K).2.2
  have hi : greedyIdx ν m K j < K := (hbefore j).mpr (by omega)
  have hnext : greedyIdx ν m K (j + 1) < K := (hbefore (j + 1)).mpr (by omega)
  rw [greedyIdx, if_pos hi] at hnext
  have hfull := greedyNext_full_of_lt ν K (1 / (64 * m ^ 2)) (greedyIdx ν m K j) hnext
  simpa only [qj, rj, greedyPartition, contribution, greedyIdx, if_pos hi] using hfull

lemma greedy_intervals_upper (ν : Measure ℝ) [IsFiniteMeasure ν]
    (m : ℝ) (hm : 0 < m) (K j : ℕ) (hj : j < greedyNumIntervals ν m K) :
    qj ν (greedyPartition ν m K).2 j ≤
      1 / (64 * m ^ 2) + (1 / K) * ν.real
        (Set.Ioo ((greedyPartition ν m K).2 j) ((greedyPartition ν m K).2 (j + 1))) := by
  have hi := ((GreedyStructure.greedyNumIntervals_spec ν m K).2.2 j).mpr hj
  have hτ : (0 : ℝ) < 1 / (64 * m ^ 2) := by positivity
  have hupper := greedyNext_contribution_le ν K (1 / (64 * m ^ 2)) hτ
    (greedyIdx ν m K j) hi
  simpa only [qj, rj, greedyPartition, contribution, greedyIdx, if_pos hi] using hupper

end CalibratedMA.Randomized.GreedyThreshold


open MeasureTheory

namespace CalibratedMA.Randomized.GreedyCount

lemma grid_strictMonoOn (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) :
    StrictMonoOn γ (Set.Iic M) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro j hj
  exact hΓ.2.2.1 j hj

lemma interval_pairwiseDisjoint (K M : ℕ) (γ : ℕ → ℝ)
    (hΓ : IsGridPartition K M γ) :
    Set.PairwiseDisjoint (↑(Finset.range M)) (fun j => Set.Ioo (γ j) (γ (j + 1))) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe, Finset.mem_range] at hi hj
  apply Set.disjoint_left.mpr
  intro s hsi hsj
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hle : γ (i + 1) ≤ γ j :=
      (grid_strictMonoOn K M γ hΓ).monotoneOn
        (by change i + 1 ≤ M; omega) (by change j ≤ M; omega) (by omega)
    exact (not_lt_of_ge hle) (lt_trans hsj.1 hsi.2)
  · have hle : γ (j + 1) ≤ γ i :=
      (grid_strictMonoOn K M γ hΓ).monotoneOn
        (by change j + 1 ≤ M; omega) (by change i ≤ M; omega) (by omega)
    exact (not_lt_of_ge hle) (lt_trans hsi.1 hsj.2)

lemma sum_interval_mass_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) :
    (∑ j ∈ Finset.range M, ν.real (Set.Ioo (γ j) (γ (j + 1)))) ≤ 1 := by
  simpa using sum_measureReal_le_measureReal_univ
    (μ := ν) (fun _ _ => measurableSet_Ioo) (interval_pairwiseDisjoint K M γ hΓ)

lemma sum_interval_widths (K M : ℕ) (γ : ℕ → ℝ)
    (hΓ : IsGridPartition K M γ) :
    (∑ j ∈ Finset.range M, (γ (j + 1) - γ j)) = 1 := by
  have htel : ∀ n : ℕ, (∑ j ∈ Finset.range n, (γ (j + 1) - γ j)) = γ n - γ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [htel, hΓ.1, hΓ.2.1]
  norm_num

lemma width_add_mass_lower (m w a q : ℝ) (hm : 0 < m) (hw : 0 ≤ w) (ha : 0 ≤ a)
    (hlower : 1 / (64 * m ^ 2) ≤ q) (hupper : q ≤ w * a / 4) :
    1 / (2 * m) ≤ w + a := by
  have hden : 0 < 64 * m ^ 2 := by positivity
  have hprod : 1 ≤ 16 * m ^ 2 * w * a := by
    have h := (div_le_iff₀ hden).mp (hlower.trans hupper)
    nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 2 * m)).mpr
  nlinarith [sq_nonneg (m * w - m * a), mul_nonneg hm.le hw, mul_nonneg hm.le ha]

/-- A partition with every interval except its last at the greedy threshold has
at most `4m + 1` intervals, hence satisfies the advertised `4m + 2` bound. -/
lemma interval_count_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (m : ℝ) (hm : 2 ≤ m)
    (hlower : ∀ j < M - 1, 1 / (64 * m ^ 2) ≤ qj ν γ j) :
    (M : ℝ) ≤ 4 * m + 2 := by
  have hmpos : 0 < m := by linarith
  have hupper (j : ℕ) : qj ν γ j ≤
      (γ (j + 1) - γ j) * ν.real (Set.Ioo (γ j) (γ (j + 1))) / 4 := by
    rw [GreedyContribution.qj_eq_contribution]
    convert GreedyContribution.contribution_le_quarter ν (γ j) (γ (j + 1)) using 1
    ring
  have hM : 0 < M := by
    by_contra h
    have hzero : M = 0 := by omega
    have hends := hΓ.2.1
    rw [hzero, hΓ.1] at hends
    norm_num at hends
  have hnonneg : ∀ j ∈ Finset.range M,
      0 ≤ (γ (j + 1) - γ j) + ν.real (Set.Ioo (γ j) (γ (j + 1))) := by
    intro j hj
    exact add_nonneg (sub_nonneg.mpr (hΓ.2.2.1 j (Finset.mem_range.mp hj)).le)
      (measureReal_nonneg)
  have hsum_lower : ((M - 1 : ℕ) : ℝ) * (1 / (2 * m)) ≤
      ∑ j ∈ Finset.range (M - 1),
        ((γ (j + 1) - γ j) + ν.real (Set.Ioo (γ j) (γ (j + 1)))) := by
    calc
      ((M - 1 : ℕ) : ℝ) * (1 / (2 * m)) =
          ∑ _j ∈ Finset.range (M - 1), (1 / (2 * m)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj =>
        width_add_mass_lower m _ _ _ hmpos
          (sub_nonneg.mpr (hΓ.2.2.1 j (by have := Finset.mem_range.mp hj; omega)).le)
          (measureReal_nonneg) (hlower j (Finset.mem_range.mp hj))
          (hupper j)
  have hsum_upper : (∑ j ∈ Finset.range (M - 1),
        ((γ (j + 1) - γ j) + ν.real (Set.Ioo (γ j) (γ (j + 1))))) ≤ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range M,
          ((γ (j + 1) - γ j) + ν.real (Set.Ioo (γ j) (γ (j + 1)))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        intro j hj _
        exact hnonneg j hj
      _ = 1 + ∑ j ∈ Finset.range M, ν.real (Set.Ioo (γ j) (γ (j + 1))) := by
        rw [Finset.sum_add_distrib, sum_interval_widths K M γ hΓ]
      _ ≤ 2 := by linarith [sum_interval_mass_le_one ν K M γ hΓ]
  have hcount : ((M - 1 : ℕ) : ℝ) ≤ 4 * m := by
    have h := hsum_lower.trans hsum_upper
    have h' : ((M - 1 : ℕ) : ℝ) / (2 * m) ≤ 2 := by simpa [div_eq_mul_inv] using h
    have h'' := (div_le_iff₀ (by positivity : 0 < 2 * m)).mp h'
    linarith
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  linarith

end CalibratedMA.Randomized.GreedyCount


namespace CalibratedMA.Randomized.GreedyVariation

/-- Appending a coefficient after one at least `τ` adds at most twice its overshoot
to the variation of the sequence closed by zero. -/
lemma append_variation_le (a b τ e : ℝ) (ha : τ ≤ a) (hb : b ≤ τ + e)
    (he : 0 ≤ e) : |b - a| + b - a ≤ 2 * e := by
  have h : |b - a| ≤ 2 * e - (b - a) := by
    apply abs_le.mpr
    constructor <;> linarith
  linarith

/-- A sequence above a common threshold except possibly at its final coefficient
has variation controlled by the threshold and the sum of its overshoot budgets. -/
lemma endpoint_variation_le (M : ℕ) (hM : 0 < M) (τ : ℝ) (q e : ℕ → ℝ)
    (hq : ∀ j < M, 0 ≤ q j) (he : ∀ j < M, 0 ≤ e j)
    (hlower : ∀ j < M - 1, τ ≤ q j) (hupper : ∀ j < M, q j ≤ τ + e j) :
    q 0 + q (M - 1) + ∑ j ∈ Finset.Ico 1 M, |q j - q (j - 1)| ≤
      2 * τ + 2 * ∑ j ∈ Finset.range M, e j := by
  induction M with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have h := hupper 0 (by omega)
      norm_num
      linarith
    | succ n =>
      have hprev := ih (by omega)
        (fun j hj => hq j (by omega))
        (fun j hj => he j (by omega))
        (fun j hj => hlower j (by omega))
        (fun j hj => hupper j (by omega))
      have hstep := append_variation_le (q n) (q (n + 1)) τ (e (n + 1))
        (hlower n (by omega)) (hupper (n + 1) (by omega)) (he (n + 1) (by omega))
      simp only [Nat.succ_sub_one] at hprev ⊢
      rw [Finset.sum_Ico_succ_top (by omega), Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel]
      linarith

/-- Separate the two boundary contributions in a zero-extended variation sum. -/
lemma variation_sum_endpoints (M : ℕ) (hM : 0 < M) (q : ℕ → ℝ)
    (hzero : 0 ≤ q 0) (hlast : 0 ≤ q (M - 1)) :
    let qzero : ℕ → ℝ := fun j => if j < M then q j else 0
    let qprev : ℕ → ℝ := fun j => if j = 0 then 0 else qzero (j - 1)
    (∑ j ∈ Finset.range (M + 1), |qzero j - qprev j|) =
      q 0 + q (M - 1) + ∑ j ∈ Finset.Ico 1 M, |q j - q (j - 1)| := by
  let v : ℕ → ℝ := fun j =>
    |(if j < M then q j else 0) - (if j = 0 then 0 else if j - 1 < M then q (j - 1) else 0)|
  change (∑ j ∈ Finset.range (M + 1), v j) = _
  have hvzero : v 0 = q 0 := by simp [v, hM, abs_of_nonneg hzero]
  have hvlast : v M = q (M - 1) := by
    have hpred : M - 1 < M := by omega
    simp [v, Nat.ne_of_gt hM, hpred, abs_of_nonneg hlast]
  have hmiddle : (∑ j ∈ Finset.Ico 1 M, v j) =
      ∑ j ∈ Finset.Ico 1 M, |q j - q (j - 1)| := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjM⟩ := Finset.mem_Ico.mp hj
    have hjne : j ≠ 0 := by omega
    have hpred : j - 1 < M := by omega
    simp [v, hjM, hjne, hpred]
  rw [Finset.sum_range_succ, Finset.sum_range_eq_add_Ico _ hM, hvzero, hvlast, hmiddle]
  ring

/-- Overshoots bounded by `ρ` times disjoint probability masses contribute at most `2ρ`. -/
lemma endpoint_variation_le_of_weighted_overshoot
    (M : ℕ) (hM : 0 < M) (τ ρ : ℝ) (q w : ℕ → ℝ)
    (hρ : 0 ≤ ρ) (hq : ∀ j < M, 0 ≤ q j) (hw : ∀ j < M, 0 ≤ w j)
    (hmass : ∑ j ∈ Finset.range M, w j ≤ 1)
    (hlower : ∀ j < M - 1, τ ≤ q j)
    (hupper : ∀ j < M, q j ≤ τ + ρ * w j) :
    q 0 + q (M - 1) + ∑ j ∈ Finset.Ico 1 M, |q j - q (j - 1)| ≤
      2 * τ + 2 * ρ := by
  have h := endpoint_variation_le M hM τ q (fun j => ρ * w j) hq
    (fun j hj => mul_nonneg hρ (hw j hj)) hlower hupper
  rw [← Finset.mul_sum] at h
  have hmass' := mul_le_mul_of_nonneg_left hmass hρ
  linarith

/-- Finite variation bound used by the greedy partition: all but the final coefficient
reach `τ`, every coefficient has a mass-weighted overshoot, and the masses sum to at most one. -/
lemma variation_le_of_weighted_overshoot
    (M : ℕ) (hM : 0 < M) (τ ρ : ℝ) (q w : ℕ → ℝ)
    (hρ : 0 ≤ ρ) (hq : ∀ j < M, 0 ≤ q j) (hw : ∀ j < M, 0 ≤ w j)
    (hmass : ∑ j ∈ Finset.range M, w j ≤ 1)
    (hlower : ∀ j < M - 1, τ ≤ q j)
    (hupper : ∀ j < M, q j ≤ τ + ρ * w j) :
    let qzero : ℕ → ℝ := fun j => if j < M then q j else 0
    let qprev : ℕ → ℝ := fun j => if j = 0 then 0 else qzero (j - 1)
    (∑ j ∈ Finset.range (M + 1), |qzero j - qprev j|) ≤ 2 * τ + 2 * ρ := by
  dsimp only
  rw [variation_sum_endpoints M hM q (hq 0 hM) (hq (M - 1) (by omega))]
  exact endpoint_variation_le_of_weighted_overshoot M hM τ ρ q w hρ hq hw hmass hlower hupper

end CalibratedMA.Randomized.GreedyVariation


open MeasureTheory
open CalibratedMA.Randomized

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      ∀ (m : ℝ) (K : ℕ), 2 ≤ m → 1 ≤ K → (1 : ℝ) / K ≤ (m ^ 2)⁻¹ →
        IsGridPartition K (greedyPartition ν m K).1 (greedyPartition ν m K).2 ∧
        ((greedyPartition ν m K).1 : ℝ) ≤ 4 * m + 2 ∧
        RoundErr ν (greedyPartition ν m K).1 (greedyPartition ν m K).2 ≤ C / m ^ 2 := by
  refine ⟨3, by norm_num, ?_⟩
  intro ν hprob hν m K hm hK hρ
  let : IsProbabilityMeasure ν := hprob
  have hmpos : 0 < m := by linarith
  have hΓ := GreedyStructure.greedyPartition_isGridPartition ν m K hK
  have hM := GreedyStructure.greedyNumIntervals_pos ν m K hK
  have hfull := GreedyThreshold.greedy_intervals_full ν m K
  refine ⟨hΓ, GreedyCount.interval_count_le ν K _ _ hΓ m hm hfull, ?_⟩
  have herr := (lemma_3_3 K _ _ hΓ ν hν).2.1
  rw [herr]
  have hbound := GreedyVariation.endpoint_variation_le_of_weighted_overshoot
    (greedyPartition ν m K).1 hM (1 / (64 * m ^ 2)) (1 / K)
    (qj ν (greedyPartition ν m K).2)
    (fun j => ν.real (Set.Ioo ((greedyPartition ν m K).2 j)
      ((greedyPartition ν m K).2 (j + 1))))
    (by positivity)
    (fun j _ => GreedyContribution.contribution_nonneg ν _ _)
    (fun _ _ => measureReal_nonneg)
    (GreedyCount.sum_interval_mass_le_one ν K _ _ hΓ)
    hfull (GreedyThreshold.greedy_intervals_upper ν m hmpos K)
  apply hbound.trans
  have hrho : (1 : ℝ) / K ≤ 1 / m ^ 2 := by simpa [one_div] using hρ
  calc
    2 * (1 / (64 * m ^ 2)) + 2 * (1 / K) ≤
        2 * (1 / (64 * m ^ 2)) + 2 * (1 / m ^ 2) := by linarith
    _ = (65 / 32 : ℝ) / m ^ 2 := by field_simp; ring
    _ ≤ 3 / m ^ 2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg m)
