-- Prove2me | solution 1 for BwSC.LowerBound.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:30:00.637983+00:00
-- url     : https://prove2.me/submissions/1e106384-428c-4f4e-a481-ad51e9698866

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.L8Aux

lemma iSup_update {K : ℕ} (k : Fin K) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (⨆ i, Function.update (0 : Fin K → ℝ) k Δ i) = Δ := by
  haveI : Nonempty (Fin K) := ⟨k⟩
  apply le_antisymm
  · apply ciSup_le
    intro i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi, hΔ]
  · have := le_ciSup (Set.finite_range (Function.update (0 : Fin K → ℝ) k Δ)).bddAbove k
    simpa using this

/-- On "`k` not chosen in `[lo, hi]`" (with `hi ≤ T`), the pseudo-regret under `Δ·e_k`
is at least `Δ · #{rounds in [max lo 1, hi]}`. -/
lemma regret_window {K T : ℕ} (k : Fin K) (Δ : ℝ) (hΔ : 0 ≤ Δ) (h : BanditHistory K T)
    (lo hi : ℕ) (hhi : hi ≤ T) (hE : notChosen h k lo hi) :
    Δ * ((hi - (lo - 1) : ℕ) : ℝ) ≤ regretOf (Function.update (0 : Fin K → ℝ) k Δ) h := by
  set μ := Function.update (0 : Fin K → ℝ) k Δ with hμ
  have hsup : (⨆ i, μ i) = Δ := iSup_update k Δ hΔ
  unfold regretOf
  rw [hsup]
  -- rewrite the pseudo-regret as a sum over `range T`
  set g : ℕ → ℝ := fun i => if hi' : i < T then Δ - μ (h ⟨i, hi'⟩).1 else 0 with hg
  have hsum : (T : ℝ) * Δ - ∑ t, μ (h t).1 = ∑ i ∈ Finset.range T, g i := by
    rw [← Fin.sum_univ_eq_sum_range g T]
    simp only [hg, Fin.is_lt, dif_pos]
    rw [Finset.sum_sub_distrib]
    simp
  rw [hsum]
  have hg0 : ∀ i, 0 ≤ g i := by
    intro i
    simp only [hg]
    split_ifs with hi'
    · have : μ (h ⟨i, hi'⟩).1 ≤ Δ := by
        rw [← hsup]; exact le_ciSup (Set.finite_range μ).bddAbove _
      linarith
    · exact le_rfl
  have hsub : Finset.Ico (lo - 1) hi ⊆ Finset.range T := by
    intro i hi'; simp only [Finset.mem_Ico, Finset.mem_range] at hi' ⊢; omega
  have hval : ∀ i ∈ Finset.Ico (lo - 1) hi, g i = Δ := by
    intro i hi'
    simp only [Finset.mem_Ico] at hi'
    have hiT : i < T := by omega
    simp only [hg, dif_pos hiT]
    have hne : (h ⟨i, hiT⟩).1 ≠ k := by
      intro hk
      apply hE (i + 1) (by omega) (by omega)
      simp [act, actA, actions, hk, hiT]
    rw [hμ, Function.update_of_ne hne]
    simp
  calc Δ * ((hi - (lo - 1) : ℕ) : ℝ) = ∑ i ∈ Finset.Ico (lo - 1) hi, g i := by
        rw [Finset.sum_congr rfl hval, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ Finset.range T, g i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hg0 i)

lemma armPullCount_eq {K T : ℕ} (i : Fin K) (h : BanditHistory K T) :
    (armPullCount i h : ℝ) = ∑ t : Fin T, if (h t).1 = i then (1 : ℝ) else 0 := by
  classical
  simp only [armPullCount, Finset.sum_boole]
  congr 1
  congr 1
  ext t; simp

lemma regretOf_eq {K T : ℕ} (μ : Fin K → ℝ) (h : BanditHistory K T) :
    regretOf μ h = ∑ i, ((⨆ j, μ j) - μ i) * (armPullCount i h : ℝ) := by
  classical
  simp_rw [armPullCount_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold regretOf
  rw [Finset.sum_sub_distrib]
  simp

lemma measurable_armPullCount {K T : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K T => (armPullCount i h : ℝ)) := by
  have : (fun h : BanditHistory K T => (armPullCount i h : ℝ)) =
      (fun a : Fin T → Fin K => (({t | a t = i}.toFinset.card : ℕ) : ℝ)) ∘ actions := by
    funext h; rfl
  rw [this]
  exact (measurable_of_finite _).comp measurable_actions

lemma integrable_armPullCount {K T : ℕ} (i : Fin K) (P : Measure (BanditHistory K T))
    [IsFiniteMeasure P] : Integrable (fun h => (armPullCount i h : ℝ)) P := by
  refine Integrable.of_bound (C := T) (measurable_armPullCount i).aestronglyMeasurable
    (ae_of_all _ (fun h => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have : armPullCount i h ≤ T := by
    unfold armPullCount
    exact (Finset.card_le_univ _).trans (by simp)
  exact_mod_cast this

lemma integrable_regretOf {K T : ℕ} (μ : Fin K → ℝ) (P : Measure (BanditHistory K T))
    [IsFiniteMeasure P] : Integrable (regretOf μ) P := by
  have : (regretOf μ : BanditHistory K T → ℝ) =
      fun h => ∑ i, ((⨆ j, μ j) - μ i) * (armPullCount i h : ℝ) := by
    funext h; exact regretOf_eq μ h
  rw [this]
  exact integrable_finsetSum _ (fun i _ => (integrable_armPullCount i P).const_mul _)

lemma regretOf_nonneg {K T : ℕ} (μ : Fin K → ℝ) (h : BanditHistory K T) : 0 ≤ regretOf μ h := by
  rw [regretOf_eq]
  refine Finset.sum_nonneg (fun i _ => mul_nonneg ?_ (Nat.cast_nonneg _))
  exact sub_nonneg.mpr (le_ciSup (Set.finite_range μ).bddAbove i)


lemma measurableSet_of_actions {K T : ℕ} (E : Set (BanditHistory K T))
    (hE : ∀ h h', actions h = actions h' → h ∈ E → h' ∈ E) : MeasurableSet E := by
  have : E = actions ⁻¹' (actions '' E) := by
    ext h; constructor
    · intro hh; exact ⟨h, hh, rfl⟩
    · rintro ⟨h', hh', e⟩; exact hE h' h e hh'
  rw [this]; exact measurable_actions (Set.toFinite _).measurableSet

lemma act_congr {K T : ℕ} {h h' : BanditHistory K T} (e : actions h = actions h') :
    act h = act h' := by
  funext t; simp [act, e]

lemma measurableSet_E2 (S K T j : ℕ) (k : Fin K) : MeasurableSet (E2 S K T j k) := by
  apply measurableSet_of_actions
  intro h h' e hh
  simp only [E2, notChosen, Set.mem_setOf_eq] at hh ⊢
  rw [← act_congr e]; exact hh

/-- From a pointwise bound on an event to the product form. -/
lemma setIntegral_ge {K T : ℕ} (μ : Fin K → ℝ) (P : Measure (BanditHistory K T))
    [IsFiniteMeasure P] (E : Set (BanditHistory K T)) (hE : MeasurableSet E) (c : ℝ)
    (hpt : ∀ h ∈ E, c ≤ regretOf μ h) :
    c * (P E).toReal ≤ ∫ h in E, regretOf μ h ∂P := by
  have h1 : ∫ h in E, c ∂P = c * (P E).toReal := by
    rw [setIntegral_const]; simp [Measure.real, mul_comm]
  rw [← h1]
  exact setIntegral_mono_on (integrableOn_const (by simp)) (integrable_regretOf μ P).integrableOn hE hpt

/-- The core inequality of Lemma 10 for `j ≥ 2`, with `A = y^a`, `B = y^{(1-u)a}`. -/
lemma key_real (K A B n tj tj1 : ℝ) (hK : 0 < K) (hB : 0 < B) (hAB : 2 * B ≤ A) (hn : 0 < n)
    (htj : K * (A * B) - 1 < tj) (htj1 : tj1 ≤ K * B ^ 2) (htj1pos : 0 < tj1) :
    K / (4 * n) * A ≤ 1 / (2 * n) * Real.sqrt (K / tj1) * (tj - tj1 + 1) := by
  have hs : 1 / B ≤ Real.sqrt (K / tj1) := by
    rw [show 1 / B = Real.sqrt (1 / B ^ 2) by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_sq hB.le]]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) htj1pos]; nlinarith
  have hcnt : K * (A * B) - K * B ^ 2 ≤ tj - tj1 + 1 := by linarith
  have hcnt0 : 0 ≤ K * (A * B) - K * B ^ 2 := by nlinarith
  have h1 : 1 / (2 * n) * (1 / B) * (K * (A * B) - K * B ^ 2) ≤
      1 / (2 * n) * Real.sqrt (K / tj1) * (tj - tj1 + 1) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hcnt hcnt0
    positivity
  have h2 : 1 / (2 * n) * (1 / B) * (K * (A * B) - K * B ^ 2) = K * (A - B) / (2 * n) := by
    field_simp
  rw [h2] at h1
  have h3 : K / (4 * n) * A ≤ K * (A - B) / (2 * n) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hK.le hn.le) (sub_nonneg.mpr hAB)]
  linarith

lemma rpow_grid (K T e : ℝ) (hK : 0 < K) (hT : 0 < T) :
    K ^ (1 - e) * T ^ e = K * (T / K) ^ e := by
  rw [Real.div_rpow hT.le hK.le, Real.rpow_sub hK, Real.rpow_one]
  have : 0 < K ^ e := by positivity
  field_simp

lemma aExp_ge_half (n : ℕ) : 1 / 2 ≤ aExp n ∧ aExp n ≤ 1 := by
  set t := (2 : ℝ) ^ (-(n : ℝ)) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht]; apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num); simp
  have : aExp n = 1 / (2 - t) := rfl
  rw [this]
  constructor
  · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  · rw [div_le_one (by linarith)]; linarith

end BwSC.LowerBound.L8Aux

namespace BwSC.LowerBound.L8Aux

lemma cast_sub_ge (m p : ℕ) : (m : ℝ) - p ≤ ((m - p : ℕ) : ℝ) := by
  rcases le_total p m with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]; simp; exact_mod_cast h

/-- Standing assumption in the form `2^(q+2) ≤ log₂(T/K)`. -/
lemma standing_L {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T)
    (hstand : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K))) :
    (2 : ℝ) ^ ((qIdx S K : ℝ) + 2) ≤ Real.logb 2 ((T : ℝ) / K) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h2 : (2 : ℝ) ≤ (T : ℝ) / K := by
    rw [le_div_iff₀ hK0]; exact_mod_cast (by omega : 2 * K ≤ T)
  have hL : 1 ≤ Real.logb 2 ((T : ℝ) / K) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using h2
  exact (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).mp hstand

/-- `y^(a u) ≥ 2` from `a ≥ 1/2`, `u ≥ 2^{-m}` and `log₂ y ≥ 2^{m+1}`. -/
lemma pow_ge_two (y a u m : ℝ) (hy : 0 < y) (ha : 1 / 2 ≤ a) (hu : (2 : ℝ) ^ (-m) ≤ u)
    (hL : (2 : ℝ) ^ (m + 1) ≤ Real.logb 2 y) : 2 ≤ y ^ (a * u) := by
  have hyL : y = (2 : ℝ) ^ (Real.logb 2 y) := (Real.rpow_logb (by norm_num) (by norm_num) hy).symm
  rw [hyL, ← Real.rpow_mul (by norm_num)]
  conv_lhs => rw [show (2 : ℝ) = 2 ^ (1 : ℝ) by norm_num]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hpm : (2 : ℝ) ^ (-m) * 2 ^ (m + 1) = 2 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have h0 : 0 < (2 : ℝ) ^ (-m) := by positivity
  have h1 : 0 ≤ Real.logb 2 y := le_trans (by positivity) hL
  calc (1 : ℝ) = 1 / 2 * ((2 : ℝ) ^ (-m) * 2 ^ (m + 1)) := by rw [hpm]; norm_num
    _ ≤ a * (u * Real.logb 2 y) := by
        apply mul_le_mul ha (mul_le_mul hu hL (by positivity) (by linarith)) (by positivity)
          (by linarith)
    _ = Real.logb 2 y * (a * u) := by ring

end BwSC.LowerBound.L8Aux


namespace BwSC.LowerBound.L8Aux

lemma switchCost_congr {K T : ℕ} {h h' : BanditHistory K T} (e : actions h = actions h') :
    switchCost h = switchCost h' := by
  funext n₁ n₂; simp only [switchCost, act_congr e]

lemma stopTime_congr {K T : ℕ} (S : ℕ) {h h' : BanditHistory K T} (e : actions h = actions h') :
    stopTime S h = stopTime S h' := by
  simp only [stopTime, switchCost_congr e]

lemma measurableSet_E1 (S K T j : ℕ) (k : Fin K) : MeasurableSet (E1 S K T j k) := by
  apply measurableSet_of_actions
  intro h h' e hh
  unfold E1 at hh ⊢
  split_ifs at hh ⊢ <;>
  · simp only [Set.mem_setOf_eq, notChosen, act_congr e, stopTime_congr S e] at hh
    simpa only [Set.mem_setOf_eq, notChosen] using hh


lemma iSup_update_nonpos {K : ℕ} (hK : 1 < K) (k : Fin K) (Δ : ℝ) (hΔ : Δ ≤ 0) :
    (⨆ i, Function.update (0 : Fin K → ℝ) k Δ i) = 0 := by
  haveI : Nonempty (Fin K) := ⟨k⟩
  obtain ⟨i0, hi0⟩ : ∃ i : Fin K, i ≠ k := by
    by_cases hk : k.val = 0
    · exact ⟨⟨1, hK⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
  apply le_antisymm
  · apply ciSup_le
    intro i
    by_cases hi : i = k
    · subst hi; simp [hΔ]
    · simp [Function.update_of_ne hi]
  · have := le_ciSup (Set.finite_range (Function.update (0 : Fin K → ℝ) k Δ)).bddAbove i0
    simpa [Function.update_of_ne hi0] using this

/-- If arm `k` (with mean `Δ ≤ 0`, all other means `0`) is played in every round of
`[s, T]`, the pseudo-regret is at least `(-Δ) (T - (s - 1))`. -/
lemma regret_stuck {K T : ℕ} (hK : 1 < K) (k : Fin K) (Δ : ℝ) (hΔ : Δ ≤ 0)
    (h : BanditHistory K T) (s : ℕ) (hs : ∀ t, s ≤ t → t ≤ T → 1 ≤ t → act h t = some k) :
    (-Δ) * ((T - (s - 1) : ℕ) : ℝ) ≤ regretOf (Function.update (0 : Fin K → ℝ) k Δ) h := by
  set μ := Function.update (0 : Fin K → ℝ) k Δ with hμ
  have hsup : (⨆ i, μ i) = 0 := iSup_update_nonpos hK k Δ hΔ
  unfold regretOf
  rw [hsup]
  set g : ℕ → ℝ := fun i => if hi' : i < T then - μ (h ⟨i, hi'⟩).1 else 0 with hg
  have hsum : (T : ℝ) * 0 - ∑ t, μ (h t).1 = ∑ i ∈ Finset.range T, g i := by
    rw [← Fin.sum_univ_eq_sum_range g T]
    simp only [hg, Fin.is_lt, dif_pos]
    simp
  rw [hsum]
  have hg0 : ∀ i, 0 ≤ g i := by
    intro i
    simp only [hg]
    split_ifs with hi'
    · have : μ (h ⟨i, hi'⟩).1 ≤ 0 := by
        rw [← hsup]; exact le_ciSup (Set.finite_range μ).bddAbove _
      linarith
    · exact le_rfl
  have hsub : Finset.Ico (s - 1) T ⊆ Finset.range T := by
    intro i hi'; simp only [Finset.mem_Ico, Finset.mem_range] at hi' ⊢; omega
  have hval : ∀ i ∈ Finset.Ico (s - 1) T, g i = -Δ := by
    intro i hi'
    simp only [Finset.mem_Ico] at hi'
    have hiT : i < T := hi'.2
    simp only [hg, dif_pos hiT]
    have hk : (h ⟨i, hiT⟩).1 = k := by
      have := hs (i + 1) (by omega) (by omega) (by omega)
      simp [act, actA, actions, hiT] at this
      exact this
    rw [hμ, hk]
    simp
  calc (-Δ) * ((T - (s - 1) : ℕ) : ℝ) = ∑ i ∈ Finset.Ico (s - 1) T, g i := by
        rw [Finset.sum_congr rfl hval, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ Finset.range T, g i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hg0 i)

lemma switchCost_mono {K T : ℕ} (h : BanditHistory K T) (n n' : ℕ) (hn : n ≤ n') :
    switchCost h 1 n ≤ switchCost h 1 n' := by
  unfold switchCost
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1, by omega, ht.2.2.2⟩

/-- After the budget is exhausted at `τ`, no further switch happens (given total `≤ S`). -/
lemma no_switch_after {K T : ℕ} (S : ℕ) (h : BanditHistory K T)
    (hsw : switchCost h 1 T ≤ S) (hτ : 1 ≤ stopTime S h ∧ stopTime S h ≤ T) :
    ∀ t, stopTime S h ≤ t → t ≤ T → act h t = act h (stopTime S h) := by
  set τ := stopTime S h with hτdef
  have hne : ((Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S)).Nonempty := by
    by_contra hne
    have : τ = T + 1 := by rw [hτdef]; unfold stopTime; rw [dif_neg hne]
    omega
  have hSτ : switchCost h 1 τ = S := by
    have hmem := Finset.min'_mem _ hne
    have : τ = ((Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S)).min' hne := by
      rw [hτdef]; unfold stopTime; rw [dif_pos hne]
    rw [this]; exact (Finset.mem_filter.mp hmem).2
  have hstep : ∀ t, τ ≤ t → t + 1 ≤ T → act h t = act h (t + 1) := by
    intro t ht1 ht2
    by_contra hneq
    have hsub : insert t ((Finset.range (T + 1)).filter (fun s => 1 ≤ s ∧ s + 1 ≤ τ ∧ 1 ≤ s ∧
        s + 1 ≤ T ∧ act h s ≠ act h (s + 1))) ⊆ (Finset.range (T + 1)).filter (fun s =>
        1 ≤ s ∧ s + 1 ≤ T ∧ 1 ≤ s ∧ s + 1 ≤ T ∧ act h s ≠ act h (s + 1)) := by
      intro s hs
      rw [Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by omega, by omega, by omega, by omega, hneq⟩
      · simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
        exact ⟨hs.1, hs.2.1, by omega, hs.2.2.2.1, hs.2.2.2.2⟩
    have hnot : t ∉ (Finset.range (T + 1)).filter (fun s => 1 ≤ s ∧ s + 1 ≤ τ ∧ 1 ≤ s ∧
        s + 1 ≤ T ∧ act h s ≠ act h (s + 1)) := by
      simp only [Finset.mem_filter]; omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at hc
    have e1 : switchCost h 1 τ = ((Finset.range (T + 1)).filter (fun s => 1 ≤ s ∧ s + 1 ≤ τ ∧
        1 ≤ s ∧ s + 1 ≤ T ∧ act h s ≠ act h (s + 1))).card := rfl
    have e2 : switchCost h 1 T = ((Finset.range (T + 1)).filter (fun s => 1 ≤ s ∧ s + 1 ≤ T ∧
        1 ≤ s ∧ s + 1 ≤ T ∧ act h s ≠ act h (s + 1))).card := rfl
    omega
  intro t ht1 ht2
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge t τ with hlt | hge
    · have : t + 1 = τ := by omega
      rw [this]
    · rw [← hstep t hge (by omega), ih hge (by omega)]

/-- Product form from an almost-everywhere bound on the event. -/
lemma setIntegral_ge_ae {K T : ℕ} (μ : Fin K → ℝ) (P : Measure (BanditHistory K T))
    [IsFiniteMeasure P] (E : Set (BanditHistory K T)) (hE : MeasurableSet E) (c : ℝ)
    (hpt : ∀ᵐ h ∂P, h ∈ E → c ≤ regretOf μ h) :
    c * (P E).toReal ≤ ∫ h in E, regretOf μ h ∂P := by
  have h1 : ∫ h in E, c ∂P = c * (P E).toReal := by
    rw [setIntegral_const]; simp [Measure.real, mul_comm]
  rw [← h1]
  apply setIntegral_mono_ae_restrict (integrableOn_const (by simp))
    (integrable_regretOf μ P).integrableOn
  exact (ae_restrict_iff' hE).mpr hpt

end BwSC.LowerBound.L8Aux

namespace BwSC.LowerBound.L8Aux

lemma act_stopTime_in {K T : ℕ} (S : ℕ) (h : BanditHistory K T) (k : Fin K)
    (hk : act h (stopTime S h) = some k) : 1 ≤ stopTime S h ∧ stopTime S h ≤ T := by
  by_contra hc
  have : act h (stopTime S h) = none := by simp [act, actA, hc]
  rw [this] at hk; exact absurd hk (by simp)

lemma Kr_bounds {S K : ℕ} (hK : 1 < K) :
    2 ≤ (K : ℝ) - (rIdx S K : ℝ) ∧ (K : ℝ) - (rIdx S K : ℝ) ≤ K + 1 := by
  have h1 : rIdx S K ≤ (K : ℤ) - 2 := by
    unfold rIdx qIdx
    by_cases hS : S = 0
    · subst hS; simp; omega
    · rw [if_neg hS]
      have hdm := Nat.div_add_mod (S - 1) (K - 1)
      have hlt := Nat.mod_lt (S - 1) (by omega : K - 1 > 0)
      have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
      have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
      have e : (S : ℤ) - 1 - (((S - 1) / (K - 1) : ℕ) : ℤ) * ((K : ℤ) - 1) =
          (((S - 1) % (K - 1) : ℕ) : ℤ) := by
        rw [← hS1, ← hK1]; push_cast; zify at hdm; linarith
      rw [e]
      zify at hlt; push_cast at hlt ⊢; omega
  have h2 : (-1 : ℤ) ≤ rIdx S K := by
    unfold rIdx qIdx
    by_cases hS : S = 0
    · subst hS; simp
    · rw [if_neg hS]
      have : ((S - 1) / (K - 1)) * (K - 1) ≤ S - 1 := Nat.div_mul_le_self _ _
      have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
      have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
      rw [← hK1]
      have h2 : ((((S - 1) / (K - 1)) * (K - 1) : ℕ) : ℤ) ≤ ((S - 1 : ℕ) : ℤ) := by
        exact_mod_cast this
      push_cast at h2
      omega
  have h1' : (rIdx S K : ℝ) ≤ (K : ℝ) - 2 := by exact_mod_cast h1
  have h2' : (-1 : ℝ) ≤ (rIdx S K : ℝ) := by exact_mod_cast h2
  constructor <;> linarith

end BwSC.LowerBound.L8Aux

open BwSC.LowerBound BwSC.LowerBound.L8Aux in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (hq : 1 ≤ qIdx S K)
    (hstand : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K)))
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (qIdx S K + 2)) (k : Fin K) :
    Rbad S K T *
        ((banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) (E1 S K T j k)).toReal ≤
      ∫ h in E1 S K T j k, regretOf (envAlt1 S K T j k) h
        ∂(banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) := by
  apply setIntegral_ge_ae _ _ _ (measurableSet_E1 _ _ _ _ _)
  filter_upwards [hπ (envAlt1 S K T j k)] with h hsw hE
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  -- notation
  set q := qIdx S K with hqdef
  set n : ℝ := (q : ℝ) + 2 with hn
  set a := aExp q with hadef
  obtain ⟨hm2, hmK⟩ := Kr_bounds (S := S) hK
  set m : ℝ := (K : ℝ) - (rIdx S K : ℝ) with hmdef
  have hm0 : 0 < m := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hTK2 : (2 * K : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  set y : ℝ := (T : ℝ) / m with hydef
  have hy1 : 1 ≤ y := by rw [hydef, le_div_iff₀ hm0, one_mul]; linarith
  have hy0 : 0 < y := by linarith
  have hTy : (T : ℝ) = m * y := by rw [hydef]; field_simp
  have hn2 : 2 ≤ n := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [hn]; linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨ha1, ha2⟩ := aExp_ge_half q
  rw [← hadef] at ha1 ha2
  -- the standing assumption, transferred to `y = T / (K - r)`
  have hLK := standing_L hK hT hstand
  rw [← hqdef] at hLK
  have hLy : (2 : ℝ) ^ ((q : ℝ) + 1) ≤ Real.logb 2 y := by
    have hyK : (T : ℝ) / K / 2 ≤ y := by
      rw [hydef, div_div, div_le_div_iff_of_pos_left hT0 (by positivity) hm0]; linarith
    have hpos : 0 < (T : ℝ) / K / 2 := by positivity
    have h1 : Real.logb 2 ((T : ℝ) / K / 2) ≤ Real.logb 2 y :=
      Real.logb_le_logb_of_le (by norm_num) hpos hyK
    rw [Real.logb_div (by positivity) (by norm_num), Real.logb_self_eq_one (by norm_num)] at h1
    have h2 : (2 : ℝ) ^ ((q : ℝ) + 2) = 2 * 2 ^ ((q : ℝ) + 1) := by
      rw [show (q : ℝ) + 2 = 1 + ((q : ℝ) + 1) by ring, Real.rpow_add (by norm_num)]; norm_num
    have h3 : (1 : ℝ) ≤ 2 ^ ((q : ℝ) + 1) := Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  -- exponents
  have hdef_a : a = 1 / (2 - (2 : ℝ) ^ (-(q : ℝ))) := rfl
  have hp0 : 0 < (2 : ℝ) ^ (-(q : ℝ)) := by positivity
  have hp1 : (2 : ℝ) ^ (-(q : ℝ)) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have he_le : ∀ u : ℝ, (2 : ℝ) ^ (-(q : ℝ)) ≤ u → (2 - u) * a ≤ 1 := by
    intro u hu
    rw [hdef_a, mul_one_div, div_le_one (by linarith)]; linarith
  have he_eq : (2 - (2 : ℝ) ^ (-(q : ℝ))) * a = 1 := by
    rw [hdef_a, mul_one_div]; exact div_self (by linarith)
  -- the grid
  have hgrid : ∀ i : ℕ, 1 ≤ i → (t1 S K T i : ℝ) =
      ⌊m * y ^ ((2 - (2 : ℝ) ^ (1 - (i : ℝ))) * a)⌋₊ := by
    intro i hi
    unfold t1; rw [if_neg (by omega), ← hmdef, ← hqdef, ← hadef, rpow_grid _ _ _ hm0 hT0]
  have hgridT : ∀ i : ℕ, 1 ≤ i → (2 : ℝ) ^ (-(q : ℝ)) ≤ (2 : ℝ) ^ (1 - (i : ℝ)) →
      t1 S K T i ≤ T := by
    intro i hi hu
    have h1 : t1 S K T i = ⌊m * y ^ ((2 - (2 : ℝ) ^ (1 - (i : ℝ))) * a)⌋₊ := by
      exact_mod_cast hgrid i hi
    rw [h1]
    have hx : m * y ^ ((2 - (2 : ℝ) ^ (1 - (i : ℝ))) * a) ≤ T := by
      rw [hTy]
      apply mul_le_mul_of_nonneg_left _ hm0.le
      calc y ^ ((2 - (2 : ℝ) ^ (1 - (i : ℝ))) * a) ≤ y ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hy1 (he_le _ hu)
        _ = y := Real.rpow_one y
    exact (Nat.floor_le_floor hx).trans_eq (Nat.floor_natCast T)
  -- the window `[t_{i}, ·]` with `2^{1-i} = 2u`: lower end `⌊m B²⌋`
  have hlow : ∀ i : ℕ, 1 ≤ i → ∀ u : ℝ, (2 : ℝ) ^ (1 - (i : ℝ)) = 2 * u →
      (t1 S K T i : ℝ) = ⌊m * (y ^ ((1 - u) * a)) ^ 2⌋₊ := by
    intro i hi u hu
    rw [hgrid i hi, hu, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    congr 3; push_cast; ring
  -- the core estimate for a window whose lower index has `2^{1-i} = 2u`
  have hcore : ∀ u : ℝ, (2 : ℝ) ^ (-(q : ℝ)) ≤ u → u ≤ 1 / 2 → ∀ tj tl : ℝ,
      m * y ^ ((2 - u) * a) - 1 < tj → tl ≤ m * (y ^ ((1 - u) * a)) ^ 2 → 0 < tl →
      m / (4 * n) * y ^ a ≤ 1 / (2 * n) * Real.sqrt (m / tl) * (tj - tl + 1) := by
    intro u hu hu2 tj tl htj htl htl0
    have hayu : 2 ≤ y ^ (a * u) := pow_ge_two y a u (q : ℝ) hy0 ha1 hu hLy
    set B := y ^ ((1 - u) * a) with hB
    have hB0 : 0 < B := by positivity
    have hAB : 2 * B ≤ y ^ a := by
      have : y ^ a = y ^ (a * u) * B := by rw [hB, ← Real.rpow_add hy0]; ring_nf
      rw [this]; nlinarith
    have hAB' : y ^ ((2 - u) * a) = y ^ a * B := by
      rw [hB, ← Real.rpow_add hy0]; ring_nf
    rw [hAB'] at htj
    exact key_real m (y ^ a) B n tj tl hm0 hB0 hAB (by linarith) htj htl htl0
  have hya : 1 ≤ y ^ a := Real.one_le_rpow hy1 (by linarith)
  have hR : Rbad S K T = m / (8 * n) * y ^ a := rfl
  rw [hR]
  have hR48 : m / (8 * n) * y ^ a ≤ m / (4 * n) * y ^ a := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_left hm0.le (by positivity) (by linarith)
  -- lower window end for the last two classes: `t_q = ⌊m B²⌋` with `u = 2^{-q}`
  have htq_eq : (t1 S K T q : ℝ) = ⌊m * (y ^ ((1 - (2 : ℝ) ^ (-(q : ℝ))) * a)) ^ 2⌋₊ := by
    apply hlow q hq
    rw [show (1 : ℝ) - q = 1 + (-(q : ℝ)) by ring, Real.rpow_add (by norm_num)]; norm_num
  have htq_pos : (0 : ℝ) < (t1 S K T q : ℝ) := by
    rw [htq_eq]
    have hB1 : 1 ≤ y ^ ((1 - (2 : ℝ) ^ (-(q : ℝ))) * a) := Real.one_le_rpow hy1 (mul_nonneg (by linarith) (by linarith))
    have : 1 ≤ m * (y ^ ((1 - (2 : ℝ) ^ (-(q : ℝ))) * a)) ^ 2 :=
      le_trans (by linarith) (le_mul_of_one_le_right hm0.le (one_le_pow₀ hB1))
    exact_mod_cast Nat.floor_pos.mpr this
  have htq_le : (t1 S K T q : ℝ) ≤ m * (y ^ ((1 - (2 : ℝ) ^ (-(q : ℝ))) * a)) ^ 2 := by
    rw [htq_eq]; exact Nat.floor_le (by positivity)
  have htqT : t1 S K T q ≤ T := by
    apply hgridT q hq
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- the last-two-windows estimate: `(T - t_q + 1)/2 · |Δ| ≥ R_bad`
  have hlast : m / (8 * n) * y ^ a ≤
      1 / (2 * n) * Real.sqrt (m / (t1 S K T q : ℝ)) * (((T : ℝ) - (t1 S K T q : ℝ) + 1) / 2) := by
    have := hcore _ le_rfl hp1 (T : ℝ) _ (by rw [he_eq, Real.rpow_one, ← hTy]; linarith)
      htq_le htq_pos
    have e : m / (8 * n) * y ^ a = (m / (4 * n) * y ^ a) / 2 := by ring
    rw [e]; linarith
  have hmid_def : mid1 S K T = (t1 S K T q + T) / 2 := rfl
  -- unfold the event
  unfold E1 at hE
  by_cases hjl : j = q + 2
  · -- the policy is stuck on the worst arm `k` after the budget is exhausted
    rw [if_pos hjl] at hE
    obtain ⟨hτmid, hτk, -⟩ := hE
    have hτ := act_stopTime_in S h k hτk
    have hstuck := no_switch_after S h hsw hτ
    have hΔ : Δ1 S K T j = -(1 / (2 * n) * Real.sqrt (m / (t1 S K T q : ℝ))) := by
      unfold Δ1; rw [if_neg (by omega), if_pos hjl]
    have hΔ0 : Δ1 S K T j ≤ 0 := by rw [hΔ]; simp only [neg_nonpos]; positivity
    have hw := regret_stuck hK k (Δ1 S K T j) hΔ0 h (stopTime S h)
      (fun t ht1 ht2 _ => by rw [hstuck t ht1 ht2, hτk])
    have hmid : 2 * mid1 S K T ≤ t1 S K T q + T := by rw [hmid_def]; omega
    have hcnt : ((T : ℝ) - (t1 S K T q : ℝ) + 1) / 2 ≤ ((T - (stopTime S h - 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      have : (2 * mid1 S K T : ℝ) ≤ (t1 S K T q : ℝ) + T := by exact_mod_cast hmid
      have : (stopTime S h : ℝ) ≤ mid1 S K T := by exact_mod_cast hτmid
      push_cast; linarith
    calc m / (8 * n) * y ^ a
        ≤ 1 / (2 * n) * Real.sqrt (m / (t1 S K T q : ℝ)) *
            (((T : ℝ) - (t1 S K T q : ℝ) + 1) / 2) := hlast
      _ ≤ (-Δ1 S K T j) * ((T - (stopTime S h - 1) : ℕ) : ℝ) := by
          rw [hΔ, neg_neg]; exact mul_le_mul_of_nonneg_left hcnt (by positivity)
      _ ≤ _ := hw
  · rw [if_neg hjl] at hE
    by_cases hjm : j = q + 1
    · -- the window `[t_q, ⌊(t_q + T)/2⌋]`
      rw [if_pos hjm] at hE
      have hΔ : Δ1 S K T j = 1 / (2 * n) * Real.sqrt (m / (t1 S K T q : ℝ)) := by
        unfold Δ1; rw [if_neg (by omega), if_neg hjl, show j - 1 = q by omega]
      have hΔ0 : 0 ≤ Δ1 S K T j := by rw [hΔ]; positivity
      have hmid : 2 * mid1 S K T + 1 ≥ t1 S K T q + T := by rw [hmid_def]; omega
      have hmidT : mid1 S K T ≤ T := by rw [hmid_def]; omega
      have hw := regret_window k (Δ1 S K T j) hΔ0 h _ _ hmidT hE
      have hq0 : 1 ≤ t1 S K T q := by exact_mod_cast htq_pos
      have hcnt : ((T : ℝ) - (t1 S K T q : ℝ) + 1) / 2 ≤
          ((mid1 S K T - (t1 S K T q - 1) : ℕ) : ℝ) := by
        have : (t1 S K T q + T : ℝ) ≤ 2 * (mid1 S K T : ℝ) + 1 := by exact_mod_cast hmid
        rw [Nat.cast_sub (by omega), Nat.cast_sub hq0]
        push_cast; linarith
      calc m / (8 * n) * y ^ a
          ≤ 1 / (2 * n) * Real.sqrt (m / (t1 S K T q : ℝ)) *
              (((T : ℝ) - (t1 S K T q : ℝ) + 1) / 2) := hlast
        _ ≤ Δ1 S K T j * ((mid1 S K T - (t1 S K T q - 1) : ℕ) : ℝ) := by
            rw [hΔ]; exact mul_le_mul_of_nonneg_left hcnt (by positivity)
        _ ≤ _ := hw
    · rw [if_neg hjm] at hE
      set u : ℝ := (2 : ℝ) ^ (1 - (j : ℝ)) with hu
      have hulow : (2 : ℝ) ^ (-(q : ℝ)) ≤ u := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (j : ℝ) ≤ q + 1 := by exact_mod_cast (by omega : j ≤ q + 1)
        linarith
      have hjT : t1 S K T j ≤ T := hgridT j hj1 hulow
      have hhi_gt : m * y ^ ((2 - u) * a) - 1 < (t1 S K T j : ℝ) := by
        rw [hgrid j hj1]; exact Nat.sub_one_lt_floor _
      by_cases hj1' : j = 1
      · -- first window: `Δ = 1`
        have hΔ : Δ1 S K T j = 1 := by rw [hj1']; simp [Δ1]
        have hΔ0 : (0 : ℝ) ≤ Δ1 S K T j := by rw [hΔ]; norm_num
        have hw := regret_window k (Δ1 S K T j) hΔ0 h _ _ hjT hE
        have hlo : t1 S K T (j - 1) = 0 := by rw [hj1']; simp [t1]
        have hc : (t1 S K T j : ℝ) = Δ1 S K T j * ((t1 S K T j - (t1 S K T (j - 1) - 1) : ℕ) : ℝ) := by
          rw [hΔ, hlo]; simp
        have hw' := hc.le.trans hw
        have hu1 : u = 1 := by rw [hu, hj1']; norm_num
        rw [hu1, show (2 - 1 : ℝ) * a = a by ring] at hhi_gt
        have hx : m ≤ m * y ^ a := le_mul_of_one_le_right hm0.le hya
        have h16 : m / (8 * n) * y ^ a ≤ m / 16 * y ^ a := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_left hm0.le (by norm_num) (by linarith)
        have : m / (8 * n) * y ^ a ≤ m * y ^ a - 1 := by
          have : m / 16 * y ^ a = m * y ^ a / 16 := by ring
          linarith
        exact this.trans (hhi_gt.le.trans hw')
      · -- windows `j ∈ [2, q]`
        have hj2' : 2 ≤ j := by omega
        have hu2 : u ≤ 1 / 2 := by
          rw [hu, show (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) by norm_num]
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : (2 : ℝ) ≤ j := by exact_mod_cast hj2'
          linarith
        have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        have hlo_eq : (t1 S K T (j - 1) : ℝ) = ⌊m * (y ^ ((1 - u) * a)) ^ 2⌋₊ := by
          apply hlow (j - 1) (by omega)
          rw [hcast, hu, show 1 - ((j : ℝ) - 1) = 1 + (1 - (j : ℝ)) by ring,
            Real.rpow_add (by norm_num)]
          norm_num
        have hB1 : 1 ≤ y ^ ((1 - u) * a) := Real.one_le_rpow hy1 (mul_nonneg (by linarith) (by linarith))
        have hlo_pos : (0 : ℝ) < (t1 S K T (j - 1) : ℝ) := by
          rw [hlo_eq]
          have : 1 ≤ m * (y ^ ((1 - u) * a)) ^ 2 :=
            le_trans (by linarith) (le_mul_of_one_le_right hm0.le (one_le_pow₀ hB1))
          exact_mod_cast Nat.floor_pos.mpr this
        have hlo_le : (t1 S K T (j - 1) : ℝ) ≤ m * (y ^ ((1 - u) * a)) ^ 2 := by
          rw [hlo_eq]; exact Nat.floor_le (by positivity)
        have hΔ : Δ1 S K T j = 1 / (2 * n) * Real.sqrt (m / (t1 S K T (j - 1) : ℝ)) := by
          unfold Δ1; rw [if_neg hj1', if_neg hjl]
        have hΔ0 : 0 ≤ Δ1 S K T j := by rw [hΔ]; positivity
        have hw := regret_window k (Δ1 S K T j) hΔ0 h _ _ hjT hE
        have hlo1 : 1 ≤ t1 S K T (j - 1) := by exact_mod_cast hlo_pos
        have hcnt : (t1 S K T j : ℝ) - (t1 S K T (j - 1) : ℝ) + 1 ≤
            ((t1 S K T j - (t1 S K T (j - 1) - 1) : ℕ) : ℝ) := by
          have := cast_sub_ge (t1 S K T j) (t1 S K T (j - 1) - 1)
          rw [Nat.cast_sub hlo1] at this
          push_cast at this; linarith
        have hkey := hcore u hulow hu2 _ _ hhi_gt hlo_le hlo_pos
        rw [← hΔ] at hkey
        calc m / (8 * n) * y ^ a ≤ m / (4 * n) * y ^ a := hR48
          _ ≤ Δ1 S K T j * ((t1 S K T j : ℝ) - (t1 S K T (j - 1) : ℝ) + 1) := hkey
          _ ≤ Δ1 S K T j * ((t1 S K T j - (t1 S K T (j - 1) - 1) : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hcnt hΔ0
          _ ≤ _ := hw
