-- Prove2me | solution 1 for BewleyGE.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:47:31.985019+00:00
-- url     : https://prove2.me/submissions/120ea563-7b61-413a-bb2f-7aa321f362a2

import Definitions.Def_BewleyGE_WeakConv

open MeasureTheory Filter Topology BewleyGE
open scoped BoundedContinuousFunction

section Helpers

private lemma bewley_splice_tendsto (a : ℝ) (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 a))
    (N : ℕ → ℕ) (hN : StrictMono N) :
    ∃ s : ℕ → ℝ, (∀ m : ℕ, s (N m) = x m) ∧ Tendsto s atTop (𝓝 a) := by
  classical
  let s : ℕ → ℝ := fun k => if h : ∃ m : ℕ, N m = k then x (Classical.choose h) else a
  refine ⟨s, ?_, ?_⟩
  · intro m
    have hex : ∃ j : ℕ, N j = N m := ⟨m, rfl⟩
    simp only [s, dif_pos hex]
    congr 1
    exact hN.injective (Classical.choose_spec hex)
  · intro U hU
    rw [mem_map, mem_atTop_sets]
    have haU : a ∈ U := mem_of_mem_nhds hU
    obtain ⟨M, hM⟩ := mem_atTop_sets.mp (hx hU)
    refine ⟨∑ j ∈ Finset.range M, (N j + 1), fun k hk => ?_⟩
    change s k ∈ U
    by_cases hex : ∃ m : ℕ, N m = k
    · simp only [s, dif_pos hex]
      have hm_eq : N (Classical.choose hex) = k := Classical.choose_spec hex
      have hm_ge : M ≤ Classical.choose hex := by
        by_contra hnot_ge
        have hlt : Classical.choose hex < M := Nat.lt_of_not_ge hnot_ge
        have hle : N (Classical.choose hex) + 1 ≤ ∑ j ∈ Finset.range M, (N j + 1) :=
          Finset.single_le_sum (f := fun j => N j + 1) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr hlt)
        omega
      exact hM (Classical.choose hex) hm_ge
    · simp only [s, dif_neg hex]
      exact haU

private lemma bewley_limit_continuous (w : ℕ → ℝ → ℝ) (w₀ : ℝ → ℝ)
    (hcc : ∀ (a : ℝ) (s : ℕ → ℝ), Tendsto s atTop (𝓝 a) →
      Tendsto (fun k => w k (s k)) atTop (𝓝 (w₀ a))) :
    Continuous w₀ := by
  rw [continuous_iff_seqContinuous]
  intro x a hx
  have hpt : ∀ b : ℝ, Tendsto (fun k => w k b) atTop (𝓝 (w₀ b)) :=
    fun b => hcc b (fun _ => b) tendsto_const_nhds
  have hexK : ∀ m : ℕ, ∃ K : ℕ, ∀ k ≥ K, |w k (x m) - w₀ (x m)| < 1 / ((m : ℝ) + 1) := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp (hpt (x m))) (1 / ((m : ℝ) + 1)) hpos
    exact ⟨K, fun k hk => by simpa [Real.dist_eq] using hK k hk⟩
  choose K hK using hexK
  let N : ℕ → ℕ := fun m => Nat.recOn m (K 0) (fun m prev => max (prev + 1) (K (m + 1)))
  have hN_strict : StrictMono N :=
    strictMono_nat_of_lt_succ (fun m => Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _))
  have hN_ge : ∀ m : ℕ, K m ≤ N m := by
    intro m
    cases m with
    | zero => exact le_rfl
    | succ m => exact Nat.le_max_right _ _
  have hclose : ∀ m : ℕ, |w (N m) (x m) - w₀ (x m)| < 1 / ((m : ℝ) + 1) :=
    fun m => hK m (N m) (hN_ge m)
  obtain ⟨s, hs_eq, hs_lim⟩ := bewley_splice_tendsto a x hx N hN_strict
  have hwN : Tendsto (fun m => w (N m) (x m)) atTop (𝓝 (w₀ a)) := by
    have h1 := (hcc a s hs_lim).comp hN_strict.tendsto_atTop
    simpa [Function.comp_def, hs_eq] using h1
  have hinv : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₁, hM₁⟩ := (Metric.tendsto_atTop.mp hwN) (ε / 2) (half_pos hε)
  obtain ⟨M₂, hM₂⟩ := (Metric.tendsto_atTop.mp hinv) (ε / 2) (half_pos hε)
  refine ⟨max M₁ M₂, fun m hm => ?_⟩
  dsimp only [Function.comp_apply]
  have d1 := hM₁ m (le_trans (le_max_left _ _) hm)
  have d2 := hM₂ m (le_trans (le_max_right _ _) hm)
  have d3 := hclose m
  rw [Real.dist_eq] at d1 d2 ⊢
  have hpos_inv : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
  rw [sub_zero, abs_of_nonneg hpos_inv] at d2
  have htri : |w₀ (x m) - w₀ a| ≤ |w (N m) (x m) - w₀ (x m)| + |w (N m) (x m) - w₀ a| := by
    calc
      |w₀ (x m) - w₀ a| = |(w₀ (x m) - w (N m) (x m)) + (w (N m) (x m) - w₀ a)| := by ring_nf
      _ ≤ |w₀ (x m) - w (N m) (x m)| + |w (N m) (x m) - w₀ a| := abs_add_le _ _
      _ = |w (N m) (x m) - w₀ (x m)| + |w (N m) (x m) - w₀ a| := by rw [abs_sub_comm]
  linarith

private lemma bewley_uniform_on_Icc (w : ℕ → ℝ → ℝ) (w₀ : ℝ → ℝ)
    (hw₀_cont : Continuous w₀)
    (hcc : ∀ (a : ℝ) (s : ℕ → ℝ), Tendsto s atTop (𝓝 a) →
      Tendsto (fun k => w k (s k)) atTop (𝓝 (w₀ a)))
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ a ∈ Set.Icc (-R) R, |w k a - w₀ a| ≤ ε := by
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  have hfreq : ∀ B : ℕ, ∃ k ≥ B, ∃ a ∈ Set.Icc (-R) R, ε < |w k a - w₀ a| := by
    intro B
    obtain ⟨k, hkB, hk⟩ := (Filter.frequently_atTop.mp hnot) B
    simp only [not_forall, not_le] at hk
    obtain ⟨a, ha_mem, ha_gt⟩ := hk
    exact ⟨k, hkB, a, ha_mem, ha_gt⟩
  choose kNext hkNext_ge aNext haNext_mem haNext_gt using hfreq
  let N : ℕ → ℕ := fun m => Nat.recOn m (kNext 0) (fun _ prev => kNext (prev + 1))
  have hN_strict : StrictMono N :=
    strictMono_nat_of_lt_succ (fun m => hkNext_ge (N m + 1))
  let stepIdx : ℕ → ℕ := fun m => Nat.recOn m 0 (fun m _ => N m + 1)
  have hN_eq : ∀ m : ℕ, N m = kNext (stepIdx m) := by
    intro m
    cases m <;> rfl
  let z : ℕ → ℝ := fun m => aNext (stepIdx m)
  have hz_mem : ∀ m : ℕ, z m ∈ Set.Icc (-R) R := fun m => haNext_mem (stepIdx m)
  have hz_gt : ∀ m : ℕ, ε < |w (N m) (z m) - w₀ (z m)| := by
    intro m
    rw [hN_eq m]
    exact haNext_gt (stepIdx m)
  obtain ⟨a, _, φ, hφ_strict, hφ_lim⟩ := isCompact_Icc.isSeqCompact hz_mem
  let N' : ℕ → ℕ := N ∘ φ
  have hN'_strict : StrictMono N' := hN_strict.comp hφ_strict
  let y : ℕ → ℝ := z ∘ φ
  obtain ⟨s, hs_eq, hs_lim⟩ := bewley_splice_tendsto a y hφ_lim N' hN'_strict
  have hw_sub : Tendsto (fun j => w (N' j) (y j)) atTop (𝓝 (w₀ a)) := by
    have h1 := (hcc a s hs_lim).comp hN'_strict.tendsto_atTop
    simpa [Function.comp_def, hs_eq] using h1
  have hw₀_sub : Tendsto (fun j => w₀ (y j)) atTop (𝓝 (w₀ a)) :=
    hw₀_cont.continuousAt.tendsto.comp hφ_lim
  have hdiff : Tendsto (fun j => |w (N' j) (y j) - w₀ (y j)|) atTop (𝓝 0) := by
    simpa using (hw_sub.sub hw₀_sub).abs
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hdiff) ε hε
  have hlt := hJ J le_rfl
  rw [Real.dist_eq, sub_zero, abs_abs] at hlt
  exact lt_irrefl ε (lt_trans (hz_gt (φ J)) hlt)

end Helpers

theorem solution (w : ℕ → ℝ → ℝ) (w₀ : ℝ → ℝ) (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    (hν : ∀ k, IsProbabilityMeasure (ν k)) (hν₀ : IsProbabilityMeasure ν₀)
    (hmeas : ∀ k, Measurable (w k)) (hbdd : ∃ C : ℝ, ∀ k a, |w k a| ≤ C)
    (hcc : ∀ (a : ℝ) (s : ℕ → ℝ), Tendsto s atTop (𝓝 a) →
      Tendsto (fun k => w k (s k)) atTop (𝓝 (w₀ a)))
    (hweak : WeakConv ν ν₀) :
    Tendsto (fun k => ∫ a, w k a ∂(ν k)) atTop (𝓝 (∫ a, w₀ a ∂ν₀)) := by
  obtain ⟨C₀, hC₀⟩ := hbdd
  let M : ℝ := max C₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right C₀ 0
  have hw_le : ∀ k a, |w k a| ≤ M := fun k a => le_trans (hC₀ k a) (le_max_left C₀ 0)
  have hpt : ∀ a : ℝ, Tendsto (fun k => w k a) atTop (𝓝 (w₀ a)) :=
    fun a => hcc a (fun _ => a) tendsto_const_nhds
  have hw₀_le : ∀ a : ℝ, |w₀ a| ≤ M :=
    fun a => le_of_tendsto' (hpt a).abs (fun k => hw_le k a)
  have hw₀_cont : Continuous w₀ := bewley_limit_continuous w w₀ hcc
  let w₀_bcf : ℝ →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup w₀ hw₀_cont M (fun a => by
      rw [Real.norm_eq_abs]
      exact hw₀_le a)
  let χ_fun : ℕ → ℝ → ℝ := fun n a => min 1 (max 0 (|a| - (n : ℝ)))
  have hχ_cont : ∀ n : ℕ, Continuous (χ_fun n) := fun n =>
    continuous_const.min (continuous_const.max (continuous_abs.sub continuous_const))
  have hχ_nonneg : ∀ (n : ℕ) (a : ℝ), 0 ≤ χ_fun n a := fun n a =>
    le_min zero_le_one (le_max_left _ _)
  have hχ_le_one : ∀ (n : ℕ) (a : ℝ), χ_fun n a ≤ 1 := fun n a =>
    min_le_left _ _
  let χ_bcf : ℕ → (ℝ →ᵇ ℝ) := fun n =>
    BoundedContinuousFunction.ofNormedAddCommGroup (χ_fun n) (hχ_cont n) 1 (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχ_nonneg n a)]
      exact hχ_le_one n a)
  have hχ_tendsto_zero : Tendsto (fun n : ℕ => ∫ a, χ_fun n a ∂ν₀) atTop (𝓝 0) := by
    have hdom := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := ν₀)
      (F := χ_fun) (f := fun _ => (0 : ℝ)) (bound := fun _ => (1 : ℝ))
      (fun n => (hχ_cont n).aestronglyMeasurable)
      (integrable_const (1 : ℝ))
      (fun n => Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ_nonneg n a)]
        exact hχ_le_one n a)
      (Eventually.of_forall fun a => by
        refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil |a|) (fun n hn => ?_)
        have hle : |a| ≤ (n : ℝ) := le_trans (Nat.le_ceil |a|) (Nat.cast_le.mpr hn)
        have hmax : max (0 : ℝ) (|a| - (n : ℝ)) = 0 := max_eq_left (by linarith)
        simp [χ_fun, hmax])
    simpa using hdom
  rw [Metric.tendsto_atTop]
  intro ε hε
  let M1 : ℝ := M + 1
  have hM1_pos : 0 < M1 := by linarith
  have h_eps8 : 0 < ε / (8 * M1) := by positivity
  obtain ⟨n, hn_tail⟩ := (Metric.tendsto_atTop.mp hχ_tendsto_zero) (ε / (8 * M1)) h_eps8
  have hn_ν₀ : ∫ a, χ_fun n a ∂ν₀ < ε / (8 * M1) := by
    have h0 := hn_tail n le_rfl
    have hint_nonneg : 0 ≤ ∫ a, χ_fun n a ∂ν₀ :=
      integral_nonneg (fun a => hχ_nonneg n a)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hint_nonneg] at h0
    exact h0
  have h_weak_χ : Tendsto (fun k => ∫ a, χ_fun n a ∂(ν k)) atTop (𝓝 (∫ a, χ_fun n a ∂ν₀)) :=
    hweak (χ_bcf n)
  have hev_tail : ∀ᶠ k in atTop, ∫ a, χ_fun n a ∂(ν k) < ε / (4 * M1) := by
    obtain ⟨K₁, hK₁⟩ := (Metric.tendsto_atTop.mp h_weak_χ) (ε / (8 * M1)) h_eps8
    refine Filter.eventually_atTop.mpr ⟨K₁, fun k hk => ?_⟩
    have hdist := hK₁ k hk
    rw [Real.dist_eq] at hdist
    have h1 := (abs_lt.mp hdist).2
    have h_two : ε / (8 * M1) + ε / (8 * M1) = ε / (4 * M1) := by
      field_simp [ne_of_gt hM1_pos]
      ring
    linarith
  have hev_unif : ∀ᶠ k in atTop, ∀ a ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      |w k a - w₀ a| ≤ ε / 4 :=
    bewley_uniform_on_Icc w w₀ hw₀_cont hcc ((n : ℝ) + 1) (by positivity)
  have h_weak_w₀ : Tendsto (fun k => ∫ a, w₀ a ∂(ν k)) atTop (𝓝 (∫ a, w₀ a ∂ν₀)) :=
    hweak w₀_bcf
  have hev_w₀ : ∀ᶠ k in atTop, |∫ a, w₀ a ∂(ν k) - ∫ a, w₀ a ∂ν₀| < ε / 4 := by
    obtain ⟨K₂, hK₂⟩ := (Metric.tendsto_atTop.mp h_weak_w₀) (ε / 4) (by positivity)
    exact Filter.eventually_atTop.mpr ⟨K₂, fun k hk => by simpa [Real.dist_eq] using hK₂ k hk⟩
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp (hev_tail.and (hev_unif.and hev_w₀))
  refine ⟨K₀, fun k hk => ?_⟩
  obtain ⟨hk_tail, hk_unif, hk_w₀⟩ := hK₀ k hk
  have : IsProbabilityMeasure (ν k) := hν k
  have hint_wk : Integrable (w k) (ν k) :=
    Integrable.of_bound (hmeas k).aestronglyMeasurable M
      (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hw_le k a)
  have hint_w₀ : Integrable w₀ (ν k) :=
    Integrable.of_bound hw₀_cont.aestronglyMeasurable M
      (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hw₀_le a)
  have hint_χ : Integrable (χ_fun n) (ν k) :=
    Integrable.of_bound (hχ_cont n).aestronglyMeasurable 1
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ_nonneg n a)]
        exact hχ_le_one n a)
  have h_pt_bound : ∀ a : ℝ, |w k a - w₀ a| ≤ ε / 4 + 2 * M1 * χ_fun n a := by
    intro a
    by_cases ha : a ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
    · have h1 := hk_unif a ha
      have h2 : 0 ≤ 2 * M1 * χ_fun n a := mul_nonneg (by positivity) (hχ_nonneg n a)
      linarith
    · have habs_gt : (n : ℝ) + 1 < |a| := by
        rw [Set.mem_Icc, not_and_or] at ha
        rcases ha with h1 | h2
        · have h1' : a < -((n : ℝ) + 1) := lt_of_not_ge h1
          exact lt_of_lt_of_le (by linarith) (neg_le_abs a)
        · have h2' : (n : ℝ) + 1 < a := lt_of_not_ge h2
          exact lt_of_lt_of_le h2' (le_abs_self a)
      have hχ_eq : χ_fun n a = 1 := by
        have hmax_ge : 1 ≤ max 0 (|a| - (n : ℝ)) :=
          le_trans (by linarith) (le_max_right 0 (|a| - (n : ℝ)))
        exact min_eq_left hmax_ge
      have hbdd_diff : |w k a - w₀ a| ≤ 2 * M1 := by
        have htri : |w k a - w₀ a| ≤ |w k a| + |w₀ a| := abs_sub _ _
        have h1 := hw_le k a
        have h2 := hw₀_le a
        linarith
      rw [hχ_eq]
      linarith
  have h_int_diff : |∫ a, w k a ∂(ν k) - ∫ a, w₀ a ∂(ν k)| ≤
      ε / 4 + 2 * M1 * ∫ a, χ_fun n a ∂(ν k) := by
    rw [← integral_sub hint_wk hint_w₀]
    calc
      |∫ a, (w k a - w₀ a) ∂(ν k)|
          ≤ ∫ a, |w k a - w₀ a| ∂(ν k) := by
            simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun a => w k a - w₀ a)
      _ ≤ ∫ a, (ε / 4 + 2 * M1 * χ_fun n a) ∂(ν k) := by
            refine integral_mono ((hint_wk.sub hint_w₀).abs) ?_ h_pt_bound
            exact (integrable_const (ε / 4)).add (hint_χ.const_mul (2 * M1))
      _ = (∫ a, (ε / 4 : ℝ) ∂(ν k)) + ∫ a, (2 * M1 * χ_fun n a) ∂(ν k) :=
            integral_add (integrable_const (ε / 4)) (hint_χ.const_mul (2 * M1))
      _ = ε / 4 + 2 * M1 * ∫ a, χ_fun n a ∂(ν k) := by
            rw [integral_const_mul]
            simp [integral_const]
  rw [Real.dist_eq]
  have h_split : |∫ a, w k a ∂(ν k) - ∫ a, w₀ a ∂ν₀| ≤
      |∫ a, w k a ∂(ν k) - ∫ a, w₀ a ∂(ν k)| + |∫ a, w₀ a ∂(ν k) - ∫ a, w₀ a ∂ν₀| := by
    calc
      |∫ a, w k a ∂(ν k) - ∫ a, w₀ a ∂ν₀|
          = |(∫ a, w k a ∂(ν k) - ∫ a, w₀ a ∂(ν k)) + (∫ a, w₀ a ∂(ν k) - ∫ a, w₀ a ∂ν₀)| := by
            ring_nf
      _ ≤ |∫ a, w k a ∂(ν k) - ∫ a, w₀ a ∂(ν k)| + |∫ a, w₀ a ∂(ν k) - ∫ a, w₀ a ∂ν₀| :=
            abs_add_le _ _
  have h_prod : 2 * M1 * ∫ a, χ_fun n a ∂(ν k) < ε / 2 := by
    calc
      2 * M1 * ∫ a, χ_fun n a ∂(ν k) < 2 * M1 * (ε / (4 * M1)) :=
        mul_lt_mul_of_pos_left hk_tail (by positivity)
      _ = ε / 2 := by
        field_simp [ne_of_gt hM1_pos]
        ring
  linarith
