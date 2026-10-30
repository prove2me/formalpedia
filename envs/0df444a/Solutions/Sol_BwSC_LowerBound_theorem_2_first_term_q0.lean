-- Prove2me | solution 1 for BwSC.LowerBound.theorem_2_first_term_q0
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:54:59.240203+00:00
-- url     : https://prove2.me/submissions/6524cbe1-1f8c-40ec-8649-644008cefe05

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof
import Theorems.Thm_BwSC_LowerBound_lemma_6
import Theorems.Thm_BwSC_LowerBound_property_1
import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.Q0A

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

end BwSC.LowerBound.Q0A

namespace BwSC.LowerBound.Q0A

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

end BwSC.LowerBound.Q0A


namespace BwSC.LowerBound.Q0A

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

end BwSC.LowerBound.Q0A

namespace BwSC.LowerBound.Q0A

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

end BwSC.LowerBound.Q0A


namespace BwSC.LowerBound.Q0B

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

lemma gap_gaussian {K : ℕ} (μ : Fin K → ℝ) (i : Fin K) :
    banditGap (gaussianBandit μ) i = (⨆ j, μ j) - μ i := by
  simp [banditGap, banditOptimalMean, banditArmMean, gaussianBandit, integral_id_gaussianReal]

lemma regret_eq_integral {K T : ℕ} (μ : Fin K → ℝ) (π : BanditPolicy K) :
    banditRegret (gaussianBandit μ) π T =
      ∫ h, regretOf μ h ∂(banditMeasure (gaussianBandit μ) π T) := by
  rw [bandit_regret_decomposition _ (fun i => (memLp_id_gaussianReal 1).integrable le_rfl) π T]
  simp_rw [regretOf_eq]
  rw [integral_finsetSum _ (fun i _ => (integrable_armPullCount i _).const_mul _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, gap_gaussian]

lemma regret_ge_setIntegral {K T : ℕ} (μ : Fin K → ℝ) (π : BanditPolicy K)
    (E : Set (BanditHistory K T)) :
    ∫ h in E, regretOf μ h ∂(banditMeasure (gaussianBandit μ) π T) ≤
      banditRegret (gaussianBandit μ) π T := by
  rw [regret_eq_integral]
  exact setIntegral_le_integral (integrable_regretOf μ _) (ae_of_all _ (regretOf_nonneg μ))

/-- `m^(1-e) T^e ≥ m` for `e ≥ 0`, `1 ≤ m ≤ T`. -/
lemma grid_ge (m T e : ℝ) (hm : 0 < m) (hmT : m ≤ T) (he : 0 ≤ e) :
    m ≤ m ^ (1 - e) * T ^ e := by
  have hT : 0 < T := lt_of_lt_of_le hm hmT
  have e1 : m ^ (1 - e) * T ^ e = m * (T / m) ^ e := by
    rw [Real.div_rpow hT.le hm.le, Real.rpow_sub hm, Real.rpow_one]
    have : 0 < m ^ e := by positivity
    field_simp
  rw [e1]
  have : 1 ≤ (T / m) ^ e := Real.one_le_rpow (by rw [le_div_iff₀ hm]; linarith) he
  nlinarith

/-- `√(m / t) ≤ 2` when `t = ⌊x⌋₊` with `x ≥ m ≥ 2`. -/
lemma sqrt_ratio_le (m x : ℝ) (hm : 2 ≤ m) (hx : m ≤ x) :
    Real.sqrt (m / (⌊x⌋₊ : ℝ)) ≤ 2 := by
  have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have ht : m / 2 ≤ (⌊x⌋₊ : ℝ) := by linarith
  have htpos : 0 < (⌊x⌋₊ : ℝ) := by linarith
  rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ htpos]; linarith

lemma aExp_pos (q : ℕ) : 0 < aExp q := by
  have : (2 : ℝ) ^ (-(q : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num); simp
  unfold aExp
  apply div_pos one_pos; linarith

lemma two_sub_pow_nonneg (i : ℕ) (hi : 1 ≤ i) : 0 ≤ 2 - (2 : ℝ) ^ (1 - (i : ℝ)) := by
  have : (2 : ℝ) ^ (1 - (i : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi
    linarith
  linarith

lemma rIdx_le {S K : ℕ} (hK : 1 < K) : rIdx S K ≤ (K : ℤ) - 2 := by
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

lemma rIdx_ge (S K : ℕ) : (-1 : ℤ) ≤ rIdx S K := by
  unfold rIdx qIdx
  by_cases hS : S = 0
  · subst hS; simp
  · rw [if_neg hS]
    have hdm := Nat.div_add_mod (S - 1) (K - 1)
    have : ((S - 1) / (K - 1)) * (K - 1) ≤ S - 1 := Nat.div_mul_le_self _ _
    have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
    by_cases hK : K = 0
    · subst hK; simp; omega
    · have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
      rw [← hK1]
      have h2 : ((((S - 1) / (K - 1)) * (K - 1) : ℕ) : ℤ) ≤ ((S - 1 : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at h2
      omega

/-- `t^{(1)}_i ≥ (K - r)/2` for `i ≥ 1`, in the form `√((K-r)/t^{(1)}_i) ≤ 2`. -/
lemma sqrt_t1 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (i : ℕ) (hi : 1 ≤ i) :
    Real.sqrt (((K : ℝ) - (rIdx S K : ℝ)) / (t1 S K T i : ℝ)) ≤ 2 := by
  have hr1 : (rIdx S K : ℝ) ≤ (K : ℝ) - 2 := by exact_mod_cast rIdx_le (S := S) hK
  have hr2 : (-1 : ℝ) ≤ (rIdx S K : ℝ) := by exact_mod_cast rIdx_ge S K
  have hTK : (2 * K : ℝ) ≤ T := by exact_mod_cast hT
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  unfold t1
  rw [if_neg (by omega)]
  apply sqrt_ratio_le _ _ (by linarith)
  apply grid_ge _ _ _ (by linarith) (by linarith)
  exact mul_nonneg (two_sub_pow_nonneg i hi) (aExp_pos _).le

lemma abs_Δ1_le {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (hq : 1 ≤ qIdx S K) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 (qIdx S K + 2)) : |Δ1 S K T j| ≤ 1 := by
  have hn : (2 : ℝ) ≤ (qIdx S K : ℝ) + 2 := by have : (0:ℝ) ≤ qIdx S K := by positivity
                                               linarith
  have key : ∀ i, 1 ≤ i → (1 / (2 * ((qIdx S K : ℝ) + 2))) *
      Real.sqrt (((K : ℝ) - (rIdx S K : ℝ)) / (t1 S K T i : ℝ)) ≤ 1 := by
    intro i hi
    have h := sqrt_t1 (S := S) hK hT i hi
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  have hs0 : ∀ i, 0 ≤ (1 / (2 * ((qIdx S K : ℝ) + 2))) *
      Real.sqrt (((K : ℝ) - (rIdx S K : ℝ)) / (t1 S K T i : ℝ)) := fun i => by positivity
  simp only [Finset.mem_Icc] at hj
  unfold Δ1
  split_ifs with h1 h2
  · simp
  · rw [abs_neg, abs_of_nonneg (hs0 _)]; exact key _ hq
  · rw [abs_of_nonneg (hs0 _)]; exact key _ (by omega)

lemma spread_update {K : ℕ} (k : Fin K) (Δ : ℝ) (hΔ : |Δ| ≤ 1) (i i' : Fin K) :
    |Function.update (0 : Fin K → ℝ) k Δ i - Function.update (0 : Fin K → ℝ) k Δ i'| ≤ 1 := by
  by_cases hi : i = k <;> by_cases hi' : i' = k
  · subst hi; subst hi'; simp
  · subst hi; simp [Function.update_of_ne hi', hΔ]
  · subst hi'; simp [Function.update_of_ne hi, abs_neg, hΔ]
  · simp [Function.update_of_ne hi, Function.update_of_ne hi']

end BwSC.LowerBound.Q0B


namespace BwSC.LowerBound.KLAux

variable {K : ℕ}

/-- Round `n + 1` can still be recorded faithfully. -/
def active (lo hi : ℕ) (k : Fin K) {n : ℕ} (r : BanditHistory K n) : Prop :=
  n + 1 < lo ∨ (n + 1 ≤ hi ∧ ∀ s, lo ≤ s → s ≤ n → act r s ≠ some k)

lemma act_snoc_le {n : ℕ} (h : BanditHistory K n) (ax : Fin K × ℝ) (s : ℕ) (hs : s ≤ n) :
    act (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1)) s = act h s := by
  simp only [act, actA, actions]
  by_cases h1 : 1 ≤ s ∧ s ≤ n
  · rw [dif_pos ⟨h1.1, by omega⟩, dif_pos h1]
    have : (⟨s - 1, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨s - 1, by omega⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · rw [dif_neg (by omega), dif_neg h1]

lemma actA_snoc_le {n : ℕ} (h : BanditHistory K n) (ax : Fin K × ℝ) (s : ℕ) (hs : s ≤ n) :
    actA (actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1))) s =
      actA (actions h) s :=
  act_snoc_le h ax s hs

/-- The recorded value of round `n + 1`. -/
noncomputable def stepRec (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n)
    (ax : Fin K × ℝ) : Fin K × ℝ := by
  classical
  exact if (n + 1 < lo ∨ (n + 1 ≤ hi ∧ ax.1 ≠ k ∧ ∀ s, lo ≤ s → s ≤ n → act h s ≠ some k))
    then ax else (k, 0)

lemma censor_snoc (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n) (ax : Fin K × ℝ) :
    stopCensor lo hi k (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1)) =
      Fin.snoc (α := fun _ => Fin K × ℝ) (stopCensor lo hi k h) (stepRec lo hi k h ax) := by
  classical
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, stopCensor, stepRec]
    have hiff : keepRound lo hi k (actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax :
        BanditHistory K (n + 1))) (Fin.last n) ↔
        (n + 1 < lo ∨ (n + 1 ≤ hi ∧ ax.1 ≠ k ∧ ∀ s, lo ≤ s → s ≤ n → act h s ≠ some k)) := by
      unfold keepRound
      simp only [Fin.val_last, Finset.mem_Ico]
      have ha : actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1))
          (Fin.last n) = ax.1 := by simp [actions]
      rw [ha]
      constructor
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨h1, h2, fun s hs1 hs2 => ?_⟩
          have := h3 s ⟨hs1, by omega⟩
          rwa [actA_snoc_le h ax s hs2] at this
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨h1, h2, fun s hs => ?_⟩
          rw [actA_snoc_le h ax s (by omega)]
          exact h3 s hs.1 (by omega)
    by_cases hk : keepRound lo hi k (actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax :
        BanditHistory K (n + 1))) (Fin.last n)
    · rw [if_pos hk, if_pos (hiff.mp hk)]
    · rw [if_neg hk, if_neg (fun hc => hk (hiff.mpr hc))]
  · simp only [Fin.snoc_castSucc, stopCensor]
    have hiff : keepRound lo hi k (actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax :
        BanditHistory K (n + 1))) (Fin.castSucc j) ↔ keepRound lo hi k (actions h) j := by
      unfold keepRound
      simp only [Fin.coe_castSucc, Finset.mem_Ico]
      have ha : actions (Fin.snoc (α := fun _ => Fin K × ℝ) h ax : BanditHistory K (n + 1))
          (Fin.castSucc j) = actions h j := by simp [actions]
      rw [ha]
      constructor
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨h1, h2, fun s hs => ?_⟩
          have := h3 s hs
          rwa [actA_snoc_le h ax s (by omega)] at this
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨h1, h2, fun s hs => ?_⟩
          rw [actA_snoc_le h ax s (by omega)]
          exact h3 s hs
    by_cases hk : keepRound lo hi k (actions h) j
    · rw [if_pos (hiff.mpr hk), if_pos hk]
    · rw [if_neg (fun hc => hk (hiff.mp hc)), if_neg hk]

lemma act_of_out {T : ℕ} (h : BanditHistory K T) (t : ℕ) (ht : ¬ (1 ≤ t ∧ t ≤ T)) :
    act h t = none := by
  simp [act, actA, ht]

lemma act_of_in {T : ℕ} (h : BanditHistory K T) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ T) :
    act h t = some ((h ⟨t - 1, by omega⟩).1) := by
  simp [act, actA, ht, actions]

/-- The stopped record, read round by round. -/
lemma act_censor {T : ℕ} (lo hi : ℕ) (k : Fin K) (h : BanditHistory K T) (t : ℕ)
    (ht : 1 ≤ t ∧ t ≤ T) :
    act (stopCensor lo hi k h) t =
      if (t < lo ∨ (t ≤ hi ∧ act h t ≠ some k ∧ ∀ s, lo ≤ s → s < t → act h s ≠ some k))
      then act h t else some k := by
  rw [act_of_in _ t ht, act_of_in h t ht]
  have hidx : ((⟨t - 1, by omega⟩ : Fin T).val + 1) = t := by simp; omega
  have hiff : keepRound lo hi k (actions h) ⟨t - 1, by omega⟩ ↔
      (t < lo ∨ (t ≤ hi ∧ some ((h ⟨t - 1, by omega⟩).1) ≠ some k ∧
        ∀ s, lo ≤ s → s < t → act h s ≠ some k)) := by
    unfold keepRound
    rw [hidx]
    simp only [Finset.mem_Ico, ne_eq, Option.some.injEq]
    constructor
    · rintro (h1 | ⟨h1, h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2, fun s hs1 hs2 => h3 s ⟨hs1, hs2⟩⟩
    · rintro (h1 | ⟨h1, h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2, fun s hs => h3 s hs.1 hs.2⟩
  unfold stopCensor
  by_cases hk : keepRound lo hi k (actions h) ⟨t - 1, by omega⟩
  · rw [if_pos hk, if_pos (hiff.mp hk)]
  · rw [if_neg hk, if_neg (fun hc => hk (hiff.mpr hc))]


lemma active_censor_eq (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n)
    (ha : active lo hi k h) : stopCensor lo hi k h = h := by
  funext i
  unfold stopCensor
  rw [if_pos]
  unfold keepRound
  rcases ha with h1 | ⟨h1, h2⟩
  · left; omega
  · by_cases hlo : i.val + 1 < lo
    · exact Or.inl hlo
    · right
      refine ⟨by omega, ?_, fun s hs => ?_⟩
      · intro hk
        apply h2 (i.val + 1) (by omega) (by omega)
        rw [act_of_in h (i.val + 1) ⟨by omega, by omega⟩]
        simp only [Nat.add_sub_cancel]
        rw [show (⟨i.val, by omega⟩ : Fin n) = i from rfl]
        simp [actions] at hk; rw [hk]
      · rw [Finset.mem_Ico] at hs
        exact h2 s hs.1 (by omega)

lemma active_censor_iff (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n) :
    active lo hi k (stopCensor lo hi k h) ↔ active lo hi k h := by
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · exact Or.inl h1
    · right
      refine ⟨h1, fun s hs1 hs2 hc => ?_⟩
      have hv : 1 ≤ s ∧ s ≤ n := by
        by_contra hv
        rw [act_of_out h s hv] at hc; exact absurd hc (by simp)
      have := h2 s hs1 hs2
      rw [act_censor lo hi k h s hv] at this
      split_ifs at this with hcond
      · rcases hcond with hc1 | ⟨_, hc2, _⟩
        · omega
        · exact hc2 hc
      · exact this rfl
  · intro ha
    rw [active_censor_eq lo hi k h ha]; exact ha

lemma measurableSet_active (lo hi : ℕ) (k : Fin K) (n : ℕ) :
    MeasurableSet {r : BanditHistory K n | active lo hi k r} := by
  have : {r : BanditHistory K n | active lo hi k r} =
      actions ⁻¹' {a : Fin n → Fin K | n + 1 < lo ∨
        (n + 1 ≤ hi ∧ ∀ s, lo ≤ s → s ≤ n → actA a s ≠ some k)} := by
    ext r; rfl
  rw [this]; exact measurable_actions (Set.toFinite _).measurableSet

/-- The recording map of an active round. -/
noncomputable def stepMap (lo : ℕ) (k : Fin K) (n : ℕ) (ax : Fin K × ℝ) : Fin K × ℝ := by
  classical
  exact if n + 1 < lo ∨ ax.1 ≠ k then ax else (k, 0)

lemma measurable_stepMap (lo : ℕ) (k : Fin K) (n : ℕ) : Measurable (stepMap lo k n) := by
  classical
  unfold stepMap
  apply Measurable.ite _ measurable_id measurable_const
  have : {ax : Fin K × ℝ | n + 1 < lo ∨ ax.1 ≠ k} = Prod.fst ⁻¹' {a | n + 1 < lo ∨ a ≠ k} := rfl
  rw [this]; exact measurable_fst (Set.toFinite _).measurableSet

lemma stepRec_of_active (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n)
    (ha : active lo hi k h) : stepRec lo hi k h = stepMap lo k n := by
  classical
  funext ax
  unfold stepRec stepMap
  rcases ha with h1 | ⟨h1, h2⟩
  · rw [if_pos (Or.inl h1), if_pos (Or.inl h1)]
  · by_cases hk : ax.1 ≠ k
    · rw [if_pos (Or.inr ⟨h1, hk, h2⟩), if_pos (Or.inr hk)]
    · by_cases hlo : n + 1 < lo
      · rw [if_pos (Or.inl hlo), if_pos (Or.inl hlo)]
      · rw [if_neg (by tauto), if_neg (by tauto)]

lemma stepRec_of_not_active (lo hi : ℕ) (k : Fin K) {n : ℕ} (h : BanditHistory K n)
    (ha : ¬ active lo hi k h) : stepRec lo hi k h = fun _ => (k, 0) := by
  classical
  funext ax
  unfold stepRec
  rw [if_neg]
  intro hc
  apply ha
  rcases hc with h1 | ⟨h1, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h3⟩

lemma measurable_stepRec (lo hi : ℕ) (k : Fin K) (n : ℕ) :
    Measurable (fun p : BanditHistory K n × (Fin K × ℝ) => stepRec lo hi k p.1 p.2) := by
  classical
  unfold stepRec
  apply Measurable.ite _ measurable_snd measurable_const
  have hA : MeasurableSet {p : BanditHistory K n × (Fin K × ℝ) |
      ∀ s, lo ≤ s → s ≤ n → act p.1 s ≠ some k} := by
    have : {p : BanditHistory K n × (Fin K × ℝ) | ∀ s, lo ≤ s → s ≤ n → act p.1 s ≠ some k} =
        (fun p : BanditHistory K n × (Fin K × ℝ) => actions p.1) ⁻¹'
          {a | ∀ s, lo ≤ s → s ≤ n → actA a s ≠ some k} := rfl
    rw [this]
    exact (measurable_actions.comp measurable_fst) (Set.toFinite _).measurableSet
  have hB : MeasurableSet {p : BanditHistory K n × (Fin K × ℝ) | p.2.1 ≠ k} := by
    have : {p : BanditHistory K n × (Fin K × ℝ) | p.2.1 ≠ k} =
        (fun p : BanditHistory K n × (Fin K × ℝ) => p.2.1) ⁻¹' {a | a ≠ k} := rfl
    rw [this]; exact (measurable_fst.comp measurable_snd) (Set.toFinite _).measurableSet
  have : {p : BanditHistory K n × (Fin K × ℝ) | n + 1 < lo ∨ (n + 1 ≤ hi ∧ p.2.1 ≠ k ∧
      ∀ s, lo ≤ s → s ≤ n → act p.1 s ≠ some k)} =
      {_p | n + 1 < lo} ∪ ({_p | n + 1 ≤ hi} ∩ ({p | p.2.1 ≠ k} ∩
        {p : BanditHistory K n × (Fin K × ℝ) | ∀ s, lo ≤ s → s ≤ n → act p.1 s ≠ some k})) := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
  rw [this]
  exact (MeasurableSet.const _).union ((MeasurableSet.const _).inter (hB.inter hA))

open Classical in
/-- The kernel generating the next recorded round from the record so far. -/
noncomputable def eta (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) : Kernel (BanditHistory K n) (Fin K × ℝ) :=
  Kernel.piecewise (measurableSet_active lo hi k n)
    ((banditStepKernel ν π n).map (stepMap lo k n)) (Kernel.const _ (Measure.dirac (k, 0)))

instance eta_markov (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) : IsMarkovKernel (eta ν π lo hi k n) := by
  haveI := Kernel.IsMarkovKernel.map (banditStepKernel ν π n) (measurable_stepMap lo k n)
  unfold eta; infer_instance

lemma eta_apply_active (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    {n : ℕ} (r : BanditHistory K n) (ha : active lo hi k r) :
    eta ν π lo hi k n r = (banditStepKernel ν π n r).map (stepMap lo k n) := by
  classical
  unfold eta
  rw [Kernel.piecewise_apply, if_pos (show r ∈ {r | active lo hi k r} from ha),
    Kernel.map_apply _ (measurable_stepMap lo k n)]

lemma eta_apply_not_active (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ)
    (k : Fin K) {n : ℕ} (r : BanditHistory K n) (ha : ¬ active lo hi k r) :
    eta ν π lo hi k n r = Measure.dirac (k, 0) := by
  classical
  unfold eta
  rw [Kernel.piecewise_apply, if_neg (show r ∉ {r | active lo hi k r} from ha), Kernel.const_apply]

/-- Push-forward of a composition product by a fibred map. -/
lemma compProd_map_pair {α β α' β' : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β'] (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → α') (hf : Measurable f) (g : α → β → β')
    (hg : Measurable (fun p : α × β => g p.1 p.2)) (η : Kernel α' β') [IsSFiniteKernel η]
    (hη : ∀ a, (κ a).map (g a) = η (f a)) :
    (μ ⊗ₘ κ).map (fun p => (f p.1, g p.1 p.2)) = (μ.map f) ⊗ₘ η := by
  have hm : Measurable (fun p : α × β => (f p.1, g p.1 p.2)) :=
    (hf.comp measurable_fst).prodMk hg
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left (κ := η) hs) hf]
  congr 1
  funext a
  rw [← hη a]
  have hga : Measurable (g a) := hg.comp measurable_prodMk_left
  rw [Measure.map_apply hga (measurable_prodMk_left hs)]
  rfl


/-- The law of the stopped record after `n` rounds. -/
noncomputable def recLaw (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) : Measure (BanditHistory K n) :=
  (banditMeasure ν π n).map (stopCensor lo hi k)

instance recLaw_prob (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) : IsProbabilityMeasure (recLaw ν π lo hi k n) :=
  Measure.isProbabilityMeasure_map (measurable_stopCensor lo hi k).aemeasurable

theorem rec_factor (ν : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (n : ℕ) :
    recLaw ν π lo hi k (n + 1) =
      ((recLaw ν π lo hi k n) ⊗ₘ eta ν π lo hi k n).map
        (fun p => (Fin.snoc (α := fun _ => Fin K × ℝ) p.1 p.2 : BanditHistory K (n + 1))) := by
  unfold recLaw
  rw [banditMeasure, Measure.map_map (measurable_stopCensor lo hi k) measurable_banditHistorySnoc]
  have hcomp : (stopCensor lo hi k) ∘ (fun p : BanditHistory K n × (Fin K × ℝ) =>
      (Fin.snoc (α := fun _ => Fin K × ℝ) p.1 p.2 : BanditHistory K (n + 1))) =
      (fun p : BanditHistory K n × (Fin K × ℝ) =>
        (Fin.snoc (α := fun _ => Fin K × ℝ) p.1 p.2 : BanditHistory K (n + 1))) ∘
      (fun p : BanditHistory K n × (Fin K × ℝ) => (stopCensor lo hi k p.1, stepRec lo hi k p.1 p.2)) := by
    funext p; exact censor_snoc lo hi k p.1 p.2
  have hpair : Measurable (fun p : BanditHistory K n × (Fin K × ℝ) =>
      (stopCensor lo hi k p.1, stepRec lo hi k p.1 p.2)) :=
    ((measurable_stopCensor lo hi k).comp measurable_fst).prodMk (measurable_stepRec lo hi k n)
  rw [hcomp, ← Measure.map_map measurable_banditHistorySnoc hpair]
  congr 1
  apply compProd_map_pair _ _ _ (measurable_stopCensor lo hi k) _ (measurable_stepRec lo hi k n)
  intro h
  by_cases ha : active lo hi k h
  · rw [eta_apply_active _ _ _ _ _ _ ((active_censor_iff lo hi k h).mpr ha),
      active_censor_eq lo hi k h ha, stepRec_of_active lo hi k h ha]
  · rw [eta_apply_not_active _ _ _ _ _ _ (fun hc => ha ((active_censor_iff lo hi k h).mp hc)),
      stepRec_of_not_active lo hi k h ha, Measure.map_const]
    simp

lemma rewardKernel_apply (ν : StochasticBandit K) (a : Fin K) :
    banditRewardKernel ν a = ν.P a := rfl

lemma step_eq (ν : StochasticBandit K) (π : BanditPolicy K) (n : ℕ) (r : BanditHistory K n) :
    banditStepKernel ν π n r = (π.select n r) ⊗ₘ banditRewardKernel ν := by
  rw [banditStepKernel, Kernel.compProd_apply_eq_compProd_sectR]
  congr 1

lemma step_ac (ν ν' : StochasticBandit K) (π : BanditPolicy K) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ)
    (r : BanditHistory K n) : banditStepKernel ν π n r ≪ banditStepKernel ν' π n r := by
  rw [step_eq, step_eq]
  apply Measure.AbsolutelyContinuous.compProd_right
  refine ae_of_all _ (fun a => ?_)
  rw [rewardKernel_apply, rewardKernel_apply]
  by_cases ha : a = k
  · subst ha; exact hac
  · rw [hdiff a ha]

lemma kl_step_kernel (ν ν' : StochasticBandit K) (π : BanditPolicy K) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ)
    (r : BanditHistory K n) :
    klDiv (banditStepKernel ν π n r) (banditStepKernel ν' π n r) =
      π.select n r {k} * klDiv (ν.P k) (ν'.P k) := by
  rw [step_eq, step_eq, klDiv_compProd_self_eq_lintegral]
  · rw [lintegral_fintype, Finset.sum_eq_single k]
    · rw [rewardKernel_apply, rewardKernel_apply, mul_comm]
    · intro b _ hb
      rw [rewardKernel_apply, rewardKernel_apply, hdiff b hb, klDiv_self]; simp
    · simp
  · intro a
    rw [rewardKernel_apply, rewardKernel_apply]
    by_cases ha : a = k
    · subst ha; exact hac
    · rw [hdiff a ha]

lemma step_map_eq (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (n : ℕ) (r : BanditHistory K n) (hlo : ¬ n + 1 < lo) :
    (banditStepKernel ν π n r).map (stepMap lo k n) =
      (banditStepKernel ν' π n r).map (stepMap lo k n) := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_stepMap lo k n) hs, Measure.map_apply (measurable_stepMap lo k n) hs,
    step_eq, step_eq, Measure.compProd_apply (measurable_stepMap lo k n hs),
    Measure.compProd_apply (measurable_stepMap lo k n hs)]
  apply lintegral_congr
  intro a
  rw [rewardKernel_apply, rewardKernel_apply]
  by_cases ha : a = k
  · subst ha
    have hset : Prod.mk a ⁻¹' (stepMap lo a n ⁻¹' s) = if (a, (0 : ℝ)) ∈ s then Set.univ else ∅ := by
      ext x
      simp only [Set.mem_preimage, stepMap, ne_eq, not_true_eq_false, or_false, if_neg hlo]
      split_ifs with h0 <;> simp [h0]
    rw [hset]
    split_ifs <;> simp
  · rw [hdiff a ha]

lemma eta_ac (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ)
    (r : BanditHistory K n) : eta ν π lo hi k n r ≪ eta ν' π lo hi k n r := by
  by_cases ha : active lo hi k r
  · rw [eta_apply_active _ _ _ _ _ r ha, eta_apply_active _ _ _ _ _ r ha]
    exact (step_ac ν ν' π k hdiff hac n r).map (measurable_stepMap lo k n)
  · rw [eta_apply_not_active _ _ _ _ _ r ha, eta_apply_not_active _ _ _ _ _ r ha]

lemma kl_eta_le (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ)
    (r : BanditHistory K n) :
    klDiv (eta ν π lo hi k n r) (eta ν' π lo hi k n r) ≤
      (if n + 1 < lo then π.select n r {k} * klDiv (ν.P k) (ν'.P k) else 0) := by
  classical
  by_cases ha : active lo hi k r
  · rw [eta_apply_active _ _ _ _ _ r ha, eta_apply_active _ _ _ _ _ r ha]
    by_cases hlo : n + 1 < lo
    · have hid : stepMap lo k n = id := by funext ax; simp [stepMap, hlo]
      rw [hid, Measure.map_id, Measure.map_id, if_pos hlo, kl_step_kernel ν ν' π k hdiff hac n r]
    · rw [step_map_eq ν ν' π lo k hdiff n r hlo, klDiv_self]; exact zero_le
  · rw [eta_apply_not_active _ _ _ _ _ r ha, eta_apply_not_active _ _ _ _ _ r ha, klDiv_self]
    exact zero_le

theorem kl_rec_step (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) (n : ℕ) :
    klDiv (recLaw ν π lo hi k (n + 1)) (recLaw ν' π lo hi k (n + 1)) ≤
      klDiv (recLaw ν π lo hi k n) (recLaw ν' π lo hi k n) +
        (if n + 1 < lo then (∫⁻ h, π.select n h {k} ∂(banditMeasure ν π n)) *
          klDiv (ν.P k) (ν'.P k) else 0) := by
  classical
  rw [rec_factor ν, rec_factor ν']
  have h1 := klDiv_map_le (μ := recLaw ν π lo hi k n ⊗ₘ eta ν π lo hi k n)
    (ν := recLaw ν' π lo hi k n ⊗ₘ eta ν' π lo hi k n) measurable_banditHistorySnoc
  rw [klDiv_compProd_eq_add, klDiv_compProd_self_eq_lintegral _ _ _
    (eta_ac ν ν' π lo hi k hdiff hac n)] at h1
  refine h1.trans (add_le_add le_rfl ?_)
  calc ∫⁻ r, klDiv (eta ν π lo hi k n r) (eta ν' π lo hi k n r) ∂(recLaw ν π lo hi k n)
      ≤ ∫⁻ r, (if n + 1 < lo then π.select n r {k} * klDiv (ν.P k) (ν'.P k) else 0)
          ∂(recLaw ν π lo hi k n) := lintegral_mono (kl_eta_le ν ν' π lo hi k hdiff hac n)
    _ = _ := by
      by_cases hlo : n + 1 < lo
      · simp only [if_pos hlo]
        rw [lintegral_mul_const _ (Kernel.measurable_coe _ (measurableSet_singleton k))]
        have hid : stopCensor lo hi k = (id : BanditHistory K n → BanditHistory K n) := by
          funext h; exact active_censor_eq lo hi k h (Or.inl hlo)
        unfold recLaw; rw [hid, Measure.map_id]
      · simp only [if_neg hlo, lintegral_zero]

theorem kl_rec_le (ν ν' : StochasticBandit K) (π : BanditPolicy K) (lo hi : ℕ) (k : Fin K)
    (hdiff : ∀ i, i ≠ k → ν.P i = ν'.P i) (hac : ν.P k ≪ ν'.P k) :
    ∀ n, klDiv (recLaw ν π lo hi k n) (recLaw ν' π lo hi k n) ≤
      ∑ t ∈ Finset.range n, (if t + 1 < lo then (∫⁻ h, π.select t h {k} ∂(banditMeasure ν π t)) *
          klDiv (ν.P k) (ν'.P k) else 0) := by
  intro n
  induction n with
  | zero =>
    have : recLaw ν π lo hi k 0 = recLaw ν' π lo hi k 0 := by
      unfold recLaw; rfl
    rw [this, klDiv_self]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    refine (kl_rec_step ν ν' π lo hi k hdiff hac n).trans ?_
    gcongr

end BwSC.LowerBound.KLAux

namespace BwSC.LowerBound.Q0D

lemma exists_ge_avg {K : ℕ} (hK : 0 < K) (m : ℕ) (f : ℕ → Fin K → ℝ) (c : ℝ)
    (h : c ≤ 1 / (((m : ℝ) + 2) * K) * ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, f j k) :
    ∃ j ∈ Finset.Icc 1 (m + 2), ∃ k : Fin K, c ≤ f j k := by
  by_contra hne
  push_neg at hne
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpos : (0 : ℝ) < ((m : ℝ) + 2) * K := by positivity
  have hne' : (Finset.Icc 1 (m + 2)).Nonempty := ⟨1, by simp⟩
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hlt : ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, f j k <
      ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, c :=
    Finset.sum_lt_sum_of_nonempty hne' (fun j hj =>
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hne j hj k))
  have hc : ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, c = ((m : ℝ) + 2) * K * c := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.card_Icc, nsmul_eq_mul]
    push_cast; ring
  rw [hc] at hlt
  have : 1 / (((m : ℝ) + 2) * K) * ∑ j ∈ Finset.Icc 1 (m + 2), ∑ k : Fin K, f j k < c := by
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]; linarith
  linarith


end BwSC.LowerBound.Q0D

open BwSC.LowerBound in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (K S T : ℕ), 1 < K → 2 * K ≤ T → qIdx S K = 0 →
      (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K)) →
      ∀ π : BanditPolicy K, IsSwitchPolicy S T π →
        ∃ μvec : Fin K → ℝ, (∀ i j, |μvec i - μvec j| ≤ 1) ∧
          C / Real.log T * rateA K S T ≤ banditRegret (gaussianBandit μvec) π T := by
  refine ⟨1 / 16, by norm_num, ?_⟩
  intro K S T hK hT hq0 _ π hπ
  classical
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hT4 : (4 : ℝ) ≤ T := by exact_mod_cast (by omega : 4 ≤ T)
  -- the phase `q = 0` means `S ≤ K - 1`, `r = S - 1`
  have hSK : S ≤ K - 1 := by
    unfold qIdx at hq0
    by_cases hS : S = 0
    · omega
    · rw [if_neg hS] at hq0
      have := (Nat.div_eq_zero_iff_lt (by omega)).mp hq0
      omega
  have hr : (rIdx S K : ℝ) = (S : ℝ) - 1 := by
    unfold rIdx; rw [hq0]; push_cast; ring
  have ha0 : aExp (qIdx S K) = 1 := by
    rw [hq0]; unfold aExp; norm_num
  have hrate : rateA K S T = ((K : ℝ) - S + 1) * T / K := by
    unfold rateA; rw [ha0, hr]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_one]; ring
  -- the two families of instances
  let Δv : ℕ → ℝ := fun j => if j = 1 then 1 else -1
  let env : ℕ → Fin K → Fin K → ℝ := fun j k => Function.update (0 : Fin K → ℝ) k (Δv j)
  -- probability transfer: the stopped record has the same law under `0` and under `env j k`
  have htrans : ∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K,
      (banditMeasure (gaussianBandit (env j k)) π T) (E1 S K T j k) =
        (banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E1 S K T j k) := by
    intro j hj k
    have hjb := Finset.mem_Icc.mp hj
    have hlo : lo1 S K T j = 0 := by
      unfold lo1; rw [if_pos (by omega), hq0]; simp [t1]
    have hpre := (property_1 (S := S) (T := T) π j hj k).1
    have hmeas := Q0A.measurableSet_E1 S K T j k
    have hkl := KLAux.kl_rec_le (gaussianBandit (0 : Fin K → ℝ)) (gaussianBandit (env j k)) π
      (lo1 S K T j) (hi1 S K T j) k
      (fun i hi => by simp [gaussianBandit, env, Function.update_of_ne hi])
      (by
        simp only [gaussianBandit, env, Pi.zero_apply, Function.update_self]
        exact (gaussianReal_absolutelyContinuous 0 one_ne_zero).trans
          (gaussianReal_absolutelyContinuous' _ one_ne_zero)) T
    rw [hlo] at hkl
    simp only [Nat.not_lt_zero, if_false, Finset.sum_const_zero, nonpos_iff_eq_zero] at hkl
    have heq := klDiv_eq_zero_iff.mp hkl
    have h1 : ∀ ν : Fin K → ℝ, (banditMeasure (gaussianBandit ν) π T) (E1 S K T j k) =
        KLAux.recLaw (gaussianBandit ν) π (lo1 S K T j) (hi1 S K T j) k T (E1 S K T j k) := by
      intro ν
      unfold KLAux.recLaw
      rw [Measure.map_apply (measurable_stopCensor _ _ _) hmeas, hpre]
    rw [h1, h1, hlo, heq]
  -- Lemma 6 under the null environment
  have h6 := lemma_6 hK hT π hπ (0 : Fin K → ℝ)
  rw [hq0] at h6
  have hceil : (⌈(S : ℝ) / ((0 : ℕ) + 1 : ℝ)⌉ : ℝ) = S := by
    push_cast; simp
  rw [hceil] at h6
  -- pathwise regret on the bad events
  have hT2 : ((T / 2 : ℕ) : ℝ) ≥ (T : ℝ) / 4 := by
    have : (T : ℝ) - 1 ≤ 2 * ((T / 2 : ℕ) : ℝ) := by
      have := Nat.div_add_mod T 2
      have hm : T % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have : (T : ℝ) = 2 * ((T / 2 : ℕ) : ℝ) + ((T % 2 : ℕ) : ℝ) := by exact_mod_cast this.symm
      have : ((T % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : T % 2 ≤ 1)
      linarith
    linarith
  have hmid : mid1 S K T = T / 2 := by
    unfold mid1; rw [hq0]; simp [t1]
  have hbad : ∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K,
      (T : ℝ) / 4 * ((banditMeasure (gaussianBandit (env j k)) π T) (E1 S K T j k)).toReal ≤
        banditRegret (gaussianBandit (env j k)) π T := by
    intro j hj k
    have hjb := Finset.mem_Icc.mp hj
    rw [hq0] at hjb
    refine le_trans ?_ (Q0B.regret_ge_setIntegral _ π (E1 S K T j k))
    apply Q0A.setIntegral_ge_ae _ _ _ (Q0A.measurableSet_E1 _ _ _ _ _)
    filter_upwards [hπ (env j k)] with h hsw hE
    unfold E1 at hE
    by_cases hj2 : j = 2
    · -- stuck on the worst arm after the budget is exhausted
      rw [if_pos (by rw [hq0]; omega)] at hE
      obtain ⟨hτmid, hτk, -⟩ := hE
      have hτ := Q0A.act_stopTime_in S h k hτk
      have hstuck := Q0A.no_switch_after S h hsw hτ
      have hΔ : Δv j = -1 := by simp [Δv, hj2]
      have hw := Q0A.regret_stuck hK k (Δv j) (by rw [hΔ]; norm_num) h (stopTime S h)
        (fun t ht1 ht2 _ => by rw [hstuck t ht1 ht2, hτk])
      rw [hmid] at hτmid
      have hcnt : (T : ℝ) / 4 ≤ ((T - (stopTime S h - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have : (stopTime S h : ℝ) ≤ ((T / 2 : ℕ) : ℝ) := by exact_mod_cast hτmid
        have : 2 * ((T / 2 : ℕ) : ℝ) ≤ T := by exact_mod_cast (Nat.mul_div_le T 2)
        push_cast; linarith
      have hc : (T : ℝ) / 4 ≤ (-Δv j) * ((T - (stopTime S h - 1) : ℕ) : ℝ) := by
        rw [hΔ, neg_neg, one_mul]; exact hcnt
      exact hc.trans hw
    · -- `k` unplayed in `[1, ⌊T/2⌋]`
      have hj1 : j = 1 := by omega
      rw [if_neg (by rw [hq0]; omega), if_pos (by rw [hq0]; omega)] at hE
      have hΔ : Δv j = 1 := by simp [Δv, hj1]
      rw [hq0, hmid] at hE
      have ht0 : t1 S K T 0 = 0 := by simp [t1]
      rw [ht0] at hE
      have hw := Q0A.regret_window k (Δv j) (by rw [hΔ]; norm_num) h 0 (T / 2) (Nat.div_le_self _ _) hE
      have hc : (T : ℝ) / 4 ≤ Δv j * ((T / 2 - (0 - 1) : ℕ) : ℝ) := by
        rw [hΔ, one_mul]; simpa using hT2
      exact hc.trans hw
  -- average over the `2K` instances
  have havg : (T : ℝ) / 4 * ((K : ℝ) - S) / (2 * K) ≤ 1 / ((((0 : ℕ) : ℝ) + 2) * K) *
      ∑ j ∈ Finset.Icc 1 (0 + 2), ∑ k : Fin K, banditRegret (gaussianBandit (env j k)) π T := by
    have hsum : (T : ℝ) / 4 * ((K : ℝ) - S) ≤ ∑ j ∈ Finset.Icc 1 (0 + 2), ∑ k : Fin K,
        banditRegret (gaussianBandit (env j k)) π T := by
      calc (T : ℝ) / 4 * ((K : ℝ) - S)
          ≤ (T : ℝ) / 4 * ∑ j ∈ Finset.Icc 1 (0 + 2), ∑ k : Fin K,
              ((banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E1 S K T j k)).toReal :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
        _ = ∑ j ∈ Finset.Icc 1 (0 + 2), ∑ k : Fin K, (T : ℝ) / 4 *
              ((banditMeasure (gaussianBandit (env j k)) π T) (E1 S K T j k)).toReal := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [htrans j (by rw [hq0]; exact hj) k]
        _ ≤ _ := Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k _ =>
              hbad j (by rw [hq0]; exact hj) k))
    have : (T : ℝ) / 4 * ((K : ℝ) - S) / (2 * K) = 1 / ((((0 : ℕ) : ℝ) + 2) * K) *
        ((T : ℝ) / 4 * ((K : ℝ) - S)) := by push_cast; field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  obtain ⟨j, hj, k, hjk⟩ := Q0D.exists_ge_avg (by omega) 0
    (fun j k => banditRegret (gaussianBandit (env j k)) π T) _ havg
  refine ⟨env j k, fun i i' => Q0B.spread_update k _ (by simp [Δv]; split_ifs <;> norm_num) i i', ?_⟩
  -- the constant
  have hlog : 1 < Real.log T := by
    have : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hSK' : (S : ℝ) + 1 ≤ K := by exact_mod_cast (by omega : S + 1 ≤ K)
  have hrate0 : 0 ≤ rateA K S T := by rw [hrate]; apply div_nonneg _ hK0.le; apply mul_nonneg <;> linarith
  calc 1 / 16 / Real.log T * rateA K S T ≤ 1 / 16 * rateA K S T := by
        apply mul_le_mul_of_nonneg_right _ hrate0
        rw [div_le_iff₀ (by linarith)]; nlinarith
    _ ≤ (T : ℝ) / 4 * ((K : ℝ) - S) / (2 * K) := by
        rw [hrate]
        have hT0 : (0 : ℝ) ≤ T := by linarith
        calc 1 / 16 * (((K : ℝ) - S + 1) * T / K) = (((K : ℝ) - S + 1) / 16) * (T / K) := by ring
          _ ≤ (((K : ℝ) - S) / 8) * (T / K) :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (T : ℝ) / 4 * ((K : ℝ) - S) / (2 * K) := by field_simp; ring
    _ ≤ _ := hjk
-- build check
