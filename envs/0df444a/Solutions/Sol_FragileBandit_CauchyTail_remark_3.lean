-- Prove2me | solution 1 for FragileBandit.CauchyTail.remark_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:33:45.106919+00:00
-- url     : https://prove2.me/submissions/72d74065-49a6-4db7-82f4-ec896c4be62b

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTRemark3Aux

lemma armPullCount_eq_sum {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h = ∑ t : Fin n, if (h t).1 = i then 1 else 0 := by
  unfold armPullCount
  rw [Set.toFinset_ofPred, Finset.card_filter]

lemma armPullCount_le {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h ≤ n := by
  rw [armPullCount_eq_sum]
  calc (∑ t : Fin n, if (h t).1 = i then 1 else 0) ≤ ∑ _t : Fin n, 1 :=
        Finset.sum_le_sum (fun t _ => by split_ifs <;> simp)
    _ = n := by simp

lemma measurable_armPullCount {K n : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K n => armPullCount i h) := by
  have hF : Measurable (fun h : BanditHistory K n => fun t => (h t).1) := by
    rw [measurable_pi_iff]
    intro t
    exact measurable_fst.comp (measurable_pi_apply t)
  have : (fun h : BanditHistory K n => armPullCount i h) =
      (fun a : Fin n → Fin K => ∑ t : Fin n, if a t = i then 1 else 0) ∘
        (fun h : BanditHistory K n => fun t => (h t).1) := by
    funext h; simp [armPullCount_eq_sum]
  rw [this]
  exact (measurable_of_countable _).comp hF

end CTRemark3Aux

namespace CTRemark3Aux

lemma measurableSet_of_count {K n : ℕ} (i : Fin K) (p : ℕ → Prop) :
    MeasurableSet {h : BanditHistory K n | p (armPullCount i h)} :=
  measurable_armPullCount i (t := {m : ℕ | p m}) MeasurableSet.of_discrete

lemma integrable_count {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (T : ℕ) : Integrable (fun h => (armPullCount i h : ℝ)) (banditMeasure ν π T) := by
  have hfm : Measurable (fun h : BanditHistory K T => (armPullCount i h : ℝ)) :=
    (measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp (measurable_armPullCount i)
  refine Integrable.of_bound hfm.aestronglyMeasurable (T : ℝ) (Filter.Eventually.of_forall ?_)
  intro h
  simp only [Real.norm_natCast]
  exact_mod_cast armPullCount_le i h

end CTRemark3Aux

open CTRemark3Aux in
theorem solution {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (c : ℝ) (hc : 0 ≤ c)
    (hE : Tendsto (fun T : ℕ => expPulls ν π T i / Real.log T) atTop (𝓝 c))
    (h32 : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      Tendsto (fun T : ℕ => banditMeasure ν π T
        {h | (1 - ε) * c ≤ (armPullCount i h : ℝ) / Real.log T}) atTop (𝓝 1)) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => banditMeasure ν π T
      {h | δ < |(armPullCount i h : ℝ) / Real.log T - c|}) atTop (𝓝 0) := by
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε' hε'
  by_cases htop : ε' = ⊤
  · exact Filter.Eventually.of_forall (fun T => by rw [htop]; exact le_top)
  set η : ℝ := ε'.toReal with hηdef
  have hη : 0 < η := ENNReal.toReal_pos hε'.ne' htop
  have hηeq : ENNReal.ofReal η = ε' := ENNReal.ofReal_toReal htop
  rw [← hηeq]
  -- choice of ε
  set ε : ℝ := min (1 / 2) (min (δ / (c + 1)) (δ * η / (4 * (c + 1)))) with hεdef
  have hc1 : 0 < c + 1 := by linarith
  have hεpos : 0 < ε := by
    rw [hεdef]; apply lt_min (by norm_num); apply lt_min <;> positivity
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεc1 : ε * c ≤ δ := by
    have h1 : ε ≤ δ / (c + 1) := le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : δ / (c + 1) * c ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc1]; nlinarith
    calc ε * c ≤ δ / (c + 1) * c := mul_le_mul_of_nonneg_right h1 hc
      _ ≤ δ := h2
  have hεc2 : ε * c ≤ δ * η / 4 := by
    have h1 : ε ≤ δ * η / (4 * (c + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : δ * η / (4 * (c + 1)) * c ≤ δ * η / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : 0 ≤ δ * η := by positivity
      nlinarith
    calc ε * c ≤ δ * η / (4 * (c + 1)) * c := mul_le_mul_of_nonneg_right h1 hc
      _ ≤ _ := h2
  -- real-valued limits
  have hA := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp (h32 ε ⟨hεpos, hε1⟩)
  simp only [ENNReal.toReal_one] at hA
  have hnum : Tendsto (fun T : ℕ => expPulls ν π T i / Real.log T - (1 - ε) * c *
      (banditMeasure ν π T {h | (1 - ε) * c ≤ (armPullCount i h : ℝ) / Real.log T}).toReal)
      atTop (𝓝 (c - (1 - ε) * c * 1)) := hE.sub (hA.const_mul _)
  have hlim_eq : c - (1 - ε) * c * 1 = ε * c := by ring
  rw [hlim_eq] at hnum
  have hev1 := hnum.eventually (gt_mem_nhds (show ε * c < ε * c + δ * η / 4 by
    have : 0 < δ * η := by positivity
    linarith))
  have hev2 := hA.eventually (lt_mem_nhds (show 1 - η / 2 < 1 by linarith))
  filter_upwards [hev1, hev2] with T hT1 hT2
  set μ := banditMeasure ν π T with hμ
  set X : BanditHistory K T → ℝ := fun h => (armPullCount i h : ℝ) / Real.log T with hX
  set A := {h : BanditHistory K T | (1 - ε) * c ≤ (armPullCount i h : ℝ) / Real.log T} with hAdef
  set B := {h : BanditHistory K T | c + δ < (armPullCount i h : ℝ) / Real.log T} with hBdef
  have hAm : MeasurableSet A := measurableSet_of_count i (fun m => (1 - ε) * c ≤ (m : ℝ) / Real.log T)
  have hBm : MeasurableSet B := measurableSet_of_count i (fun m => c + δ < (m : ℝ) / Real.log T)
  have hX0 : ∀ h, 0 ≤ X h := fun h => by
    simp only [hX]
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg T)
  -- the expectation bound
  have hXint : Integrable X μ := (integrable_count ν π i T).div_const _
  have hEX : ∫ h, X h ∂μ = expPulls ν π T i / Real.log T := by
    simp only [hX]; rw [integral_div]; rfl
  set f : BanditHistory K T → ℝ := fun h =>
    (1 - ε) * c * (A ∩ Bᶜ).indicator 1 h + (c + δ) * B.indicator 1 h with hf
  have hfX : ∀ h, f h ≤ X h := by
    intro h
    simp only [hf]
    by_cases hb : h ∈ B
    · have hnb : h ∉ A ∩ Bᶜ := fun hh => hh.2 hb
      rw [Set.indicator_of_notMem hnb, Set.indicator_of_mem hb]
      simp only [Pi.one_apply, mul_zero, mul_one, zero_add]
      exact le_of_lt hb
    · rw [Set.indicator_of_notMem hb]
      by_cases ha : h ∈ A
      · rw [Set.indicator_of_mem (show h ∈ A ∩ Bᶜ from ⟨ha, hb⟩)]
        simp only [Pi.one_apply, mul_one, mul_zero, add_zero]
        exact ha
      · have hna : h ∉ A ∩ Bᶜ := fun hh => ha hh.1
        rw [Set.indicator_of_notMem hna]
        simp only [mul_zero, add_zero]
        exact hX0 h
  have hfint : Integrable f μ := by
    simp only [hf]
    refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
    · exact (integrable_const (1 : ℝ)).indicator (hAm.inter hBm.compl)
    · exact (integrable_const (1 : ℝ)).indicator hBm
  have hfint_eq : ∫ h, f h ∂μ = (1 - ε) * c * μ.real (A ∩ Bᶜ) + (c + δ) * μ.real B := by
    simp only [hf]
    rw [integral_add, integral_const_mul, integral_const_mul,
      integral_indicator_one (hAm.inter hBm.compl), integral_indicator_one hBm]
    · exact ((integrable_const (1 : ℝ)).indicator (hAm.inter hBm.compl)).const_mul _
    · exact ((integrable_const (1 : ℝ)).indicator hBm).const_mul _
  have hmono := integral_mono hfint hXint hfX
  rw [hfint_eq, hEX] at hmono
  have hAB : μ.real A - μ.real B ≤ μ.real (A ∩ Bᶜ) := by
    have h1 : μ.real A ≤ μ.real (A ∩ Bᶜ) + μ.real B := by
      calc μ.real A ≤ μ.real ((A ∩ Bᶜ) ∪ B) := measureReal_mono (fun h ha => by
            by_cases hb : h ∈ B
            · exact Or.inr hb
            · exact Or.inl ⟨ha, hb⟩)
        _ ≤ _ := measureReal_union_le _ _
    linarith
  have h1ec : 0 ≤ (1 - ε) * c := mul_nonneg (by linarith) hc
  have hkey : (ε * c + δ) * μ.real B ≤
      expPulls ν π T i / Real.log T - (1 - ε) * c * μ.real A := by
    have := mul_le_mul_of_nonneg_left hAB h1ec
    nlinarith
  have hT1' : expPulls ν π T i / Real.log T - (1 - ε) * c * μ.real A < ε * c + δ * η / 4 := hT1
  have hT2' : 1 - η / 2 < μ.real A := hT2
  have hBle : μ.real B < η / 2 := by
    have hB0 : 0 ≤ μ.real B := measureReal_nonneg
    have : δ * μ.real B < δ * (η / 2) := by
      have h3 : δ * μ.real B ≤ (ε * c + δ) * μ.real B := by
        have : 0 ≤ ε * c := mul_nonneg hεpos.le hc
        nlinarith
      nlinarith
    exact lt_of_mul_lt_mul_left this hδ.le
  have hAc : μ.real Aᶜ < η / 2 := by
    rw [measureReal_compl hAm, probReal_univ]; linarith [hT2']
  -- the target event
  have hsub : {h : BanditHistory K T | δ < |(armPullCount i h : ℝ) / Real.log T - c|} ⊆ Aᶜ ∪ B := by
    intro h hh
    simp only [Set.mem_ofPred_eq] at hh
    rcases lt_abs.1 hh with h1 | h1
    · right; show c + δ < _; linarith
    · left
      intro ha
      have ha' : (1 - ε) * c ≤ (armPullCount i h : ℝ) / Real.log T := ha
      linarith
  have hreal : μ.real {h : BanditHistory K T | δ < |(armPullCount i h : ℝ) / Real.log T - c|} < η :=
    calc _ ≤ μ.real (Aᶜ ∪ B) := measureReal_mono hsub
      _ ≤ μ.real Aᶜ + μ.real B := measureReal_union_le _ _
      _ < η := by linarith
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal.le
