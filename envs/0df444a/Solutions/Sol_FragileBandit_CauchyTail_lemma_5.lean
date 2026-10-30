-- Prove2me | solution 1 for FragileBandit.CauchyTail.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:27:55.618592+00:00
-- url     : https://prove2.me/submissions/c54e6042-7a9f-4ae1-b9db-a8dc2e71e321

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTLemma5Aux

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


lemma armPullCount_snoc_ge {K n : ℕ} (i : Fin K) (h : BanditHistory K n) (p : Fin K × ℝ) :
    armPullCount i h ≤ armPullCount i (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) := by
  rw [armPullCount_eq_sum, armPullCount_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc]
  exact Nat.le_add_right _ _

lemma measurableSet_gt {K n : ℕ} (i : Fin K) (x : ℝ) :
    MeasurableSet {h : BanditHistory K n | x < (armPullCount i h : ℝ)} :=
  measurable_armPullCount i (t := {m : ℕ | x < (m : ℝ)}) MeasurableSet.of_discrete

lemma tail_mono_succ {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (x : ℝ) (n : ℕ) :
    banditMeasure ν π n {h | x < (armPullCount i h : ℝ)} ≤
      banditMeasure ν π (n + 1) {h | x < (armPullCount i h : ℝ)} := by
  rw [banditMeasure.eq_2, Measure.map_apply measurable_banditHistorySnoc (measurableSet_gt i x)]
  calc banditMeasure ν π n {h | x < (armPullCount i h : ℝ)}
      = ((banditMeasure ν π n).compProd (banditStepKernel ν π n)).fst
          {h | x < (armPullCount i h : ℝ)} := by rw [Measure.fst_compProd]
    _ = ((banditMeasure ν π n).compProd (banditStepKernel ν π n))
          (Prod.fst ⁻¹' {h | x < (armPullCount i h : ℝ)}) :=
        Measure.fst_apply (measurableSet_gt i x)
    _ ≤ _ := by
        apply measure_mono
        intro p hp
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
        exact lt_of_lt_of_le hp (by exact_mod_cast armPullCount_snoc_ge i p.1 p.2)

lemma tail_mono {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (x : ℝ) {n m : ℕ} (hnm : n ≤ m) :
    banditMeasure ν π n {h | x < (armPullCount i h : ℝ)} ≤
      banditMeasure ν π m {h | x < (armPullCount i h : ℝ)} :=
  monotone_nat_of_le_succ (f := fun n => banditMeasure ν π n {h | x < (armPullCount i h : ℝ)})
    (fun n => tail_mono_succ ν π i x n) hnm

end CTLemma5Aux


namespace CTLemma5Aux

lemma part_i {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (g : ℝ → ℝ)
    (hg_inf : Tendsto (fun T : ℕ => g T) atTop atTop)
    (H48 : ∀ a : ℝ, c < a → ∀ᶠ T : ℕ in atTop, ENNReal.ofReal ((T : ℝ) ^ (-a)) ≤
        banditMeasure ν π T {h | (1 - γ) * (T : ℝ) < (armPullCount i h : ℝ)}) :
    ∀ a : ℝ, c < a → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (g T) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-a)) ≤ banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} := by
  intro a ha
  obtain ⟨hγ0, hγ1⟩ := hγ
  have h1γ : 0 < 1 - γ := by linarith
  set a' : ℝ := (c + a) / 2 with ha'
  have ha'c : c < a' := by rw [ha']; linarith
  have ha'a : a' < a := by rw [ha']; linarith
  have ha'pos : 0 < a' := by linarith
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 (H48 a' ha'c)
  set C : ℝ := 1 / (1 - γ) + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hX : ∀ᶠ x : ℝ in atTop, C ^ a' ≤ x ^ (a - a') :=
    (tendsto_rpow_atTop (by linarith)).eventually (eventually_ge_atTop _)
  obtain ⟨X0, hX0⟩ := eventually_atTop.1 hX
  filter_upwards [hg_inf.eventually (eventually_ge_atTop (max (max 1 (T0 : ℝ)) X0))]
    with T hT x hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans hT hx.1)
  have hxT0 : (T0 : ℝ) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans hT hx.1)
  have hxX0 : X0 ≤ x := le_trans (le_max_right _ _) (le_trans hT hx.1)
  have hxpos : 0 < x := by linarith
  set T' : ℕ := ⌈x / (1 - γ)⌉₊ with hT'
  have hT'T : T' ≤ T := by
    rw [hT']
    apply Nat.ceil_le.2
    rw [div_le_iff₀ h1γ]
    linarith [hx.2]
  have hxT' : x / (1 - γ) ≤ T' := Nat.le_ceil _
  have hT'ge : x ≤ (1 - γ) * T' := by
    rw [div_le_iff₀ h1γ] at hxT'
    linarith
  have hxdiv : x ≤ x / (1 - γ) := le_div_self hxpos.le h1γ (by linarith)
  have hT'0 : T0 ≤ T' := by
    have : (T0 : ℝ) ≤ T' := by linarith
    exact_mod_cast this
  have hT'le : (T' : ℝ) ≤ C * x := by
    have h1 : (T' : ℝ) < x / (1 - γ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : C * x = x / (1 - γ) + x := by rw [hC]; field_simp
    linarith
  have hT'pos : (0 : ℝ) < T' := by
    have : 0 < x / (1 - γ) := by positivity
    linarith
  have key : x ^ (-a) ≤ (T' : ℝ) ^ (-a') := by
    rw [Real.rpow_neg hxpos.le, Real.rpow_neg hT'pos.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hT'pos _)
    calc (T' : ℝ) ^ a' ≤ (C * x) ^ a' := Real.rpow_le_rpow hT'pos.le hT'le ha'pos.le
      _ = C ^ a' * x ^ a' := Real.mul_rpow hCpos.le hxpos.le
      _ ≤ x ^ (a - a') * x ^ a' :=
          mul_le_mul_of_nonneg_right (hX0 x hxX0) (Real.rpow_nonneg hxpos.le _)
      _ = x ^ a := by rw [← Real.rpow_add hxpos]; congr 1; ring
  calc ENNReal.ofReal (x ^ (-a)) ≤ ENNReal.ofReal ((T' : ℝ) ^ (-a')) :=
        ENNReal.ofReal_le_ofReal key
    _ ≤ banditMeasure ν π T' {h | (1 - γ) * (T' : ℝ) < (armPullCount i h : ℝ)} := hT0 T' hT'0
    _ ≤ banditMeasure ν π T' {h | x < (armPullCount i h : ℝ)} :=
        measure_mono (fun h hh => lt_of_le_of_lt hT'ge hh)
    _ ≤ banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} := tail_mono ν π i x hT'T

lemma part_ii {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (c : ℝ) (γ : ℝ) (g : ℝ → ℝ)
    (hg_inf : Tendsto (fun T : ℕ => g T) atTop atTop)
    (hratio : Tendsto (fun n : ℕ => Real.log (g ((n : ℝ) + 1)) / Real.log (g n)) atTop (𝓝 1))
    (H50 : ∀ a : ℝ, a < c → ∀ᶠ T : ℕ in atTop,
        banditMeasure ν π T {h | g T < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (g T ^ (-a))) :
    ∀ a : ℝ, a < c → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (g T) ((1 - γ) * (T : ℝ)),
        banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (x ^ (-a)) := by
  intro a ha
  by_cases ha0 : a ≤ 0
  · filter_upwards [hg_inf.eventually (eventually_ge_atTop 1)] with T hT x hx
    calc banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (x ^ (-a)) :=
          ENNReal.ofReal_le_ofReal (Real.one_le_rpow (le_trans hT hx.1) (by linarith))
  push_neg at ha0
  set a' : ℝ := (a + c) / 2 with ha'
  have ha'c : a' < c := by rw [ha']; linarith
  have ha'a : a < a' := by rw [ha']; linarith
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 (H50 a' ha'c)
  have hlt : (1 : ℝ) < a' / a := by rw [lt_div_iff₀ ha0]; linarith
  obtain ⟨M1, hM1⟩ := eventually_atTop.1
    ((hratio.eventually (ge_mem_nhds hlt)).and (hg_inf.eventually (eventually_gt_atTop 1)))
  filter_upwards [eventually_ge_atTop (max T0 M1)] with T hT x hx
  have hTT0 : T0 ≤ T := le_trans (le_max_left _ _) hT
  have hTM1 : M1 ≤ T := le_trans (le_max_right _ _) hT
  have hgT1 : 1 < g T := (hM1 T hTM1).2
  have hxpos : 0 < x := by linarith [hx.1]
  classical
  have hex : ∃ n : ℕ, T ≤ n ∧ x < g n := by
    obtain ⟨n, hn⟩ := ((eventually_ge_atTop T).and (hg_inf.eventually (eventually_gt_atTop x))).exists
    exact ⟨n, hn⟩
  set n0 := Nat.find hex with hn0def
  have hn0 : T ≤ n0 ∧ x < g n0 := Nat.find_spec hex
  have hTn0 : T < n0 := by
    rcases lt_or_eq_of_le hn0.1 with h | h
    · exact h
    · exfalso; rw [← h] at hn0; linarith [hx.1, hn0.2]
  set m := n0 - 1 with hm
  have hmn0 : m + 1 = n0 := by omega
  have hmlt : m < n0 := by omega
  have hTm : T ≤ m := by omega
  have hnotp : ¬ (T ≤ m ∧ x < g m) := Nat.find_min hex hmlt
  have hgm : g m ≤ x := by
    by_contra hcon; push_neg at hcon; exact hnotp ⟨hTm, hcon⟩
  have hMm := hM1 m (le_trans hTM1 hTm)
  have hgm1 : 1 < g m := hMm.2
  have hlogm : 0 < Real.log (g m) := Real.log_pos hgm1
  have hxg : x < g ((m : ℝ) + 1) := by
    have := hn0.2; rw [← hmn0] at this; push_cast at this; exact this
  have hgm1pos : 0 < g ((m : ℝ) + 1) := by linarith
  have key : g m ^ (-a') ≤ x ^ (-a) := by
    rw [Real.rpow_neg (by linarith), Real.rpow_neg hxpos.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hxpos _)
    calc x ^ a ≤ g ((m : ℝ) + 1) ^ a := Real.rpow_le_rpow hxpos.le hxg.le ha0.le
      _ ≤ g m ^ a' := by
        rw [Real.rpow_def_of_pos hgm1pos, Real.rpow_def_of_pos (by linarith)]
        apply Real.exp_le_exp.2
        have h1 := hMm.1
        rw [div_le_iff₀ hlogm] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 ha0.le
        have h3 : a * (a' / a * Real.log (g m)) = a' * Real.log (g m) := by field_simp
        linarith
  calc banditMeasure ν π T {h | x < (armPullCount i h : ℝ)}
      ≤ banditMeasure ν π m {h | x < (armPullCount i h : ℝ)} := tail_mono ν π i x hTm
    _ ≤ banditMeasure ν π m {h | g m < (armPullCount i h : ℝ)} :=
        measure_mono (fun h hh => lt_of_le_of_lt hgm hh)
    _ ≤ ENNReal.ofReal (g m ^ (-a')) := hT0 m (le_trans hTT0 hTm)
    _ ≤ ENNReal.ofReal (x ^ (-a)) := ENNReal.ofReal_le_ofReal key

end CTLemma5Aux

open CTLemma5Aux in
theorem solution {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (g : ℝ → ℝ) (hg_mono : StrictMonoOn g (Set.Ioi 1)) (hg_pos : ∀ t : ℝ, 1 < t → 0 < g t)
    (hg_log : Tendsto (fun t : ℝ => g t / Real.log t) atTop atTop)
    (hg_o : Tendsto (fun t : ℝ => g t / t) atTop (𝓝 0)) :
    -- (i): (48) ⇒ (49)
    ((∀ a : ℝ, c < a → ∀ᶠ T : ℕ in atTop, ENNReal.ofReal ((T : ℝ) ^ (-a)) ≤
        banditMeasure ν π T {h | (1 - γ) * (T : ℝ) < (armPullCount i h : ℝ)}) →
      ∀ a : ℝ, c < a → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (g T) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-a)) ≤ banditMeasure ν π T {h | x < (armPullCount i h : ℝ)}) ∧
    -- (ii): (50) ⇒ (51), corrected
    (Tendsto (fun n : ℕ => Real.log (g ((n : ℝ) + 1)) / Real.log (g n)) atTop (𝓝 1) →
      (∀ a : ℝ, a < c → ∀ᶠ T : ℕ in atTop,
        banditMeasure ν π T {h | g T < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (g T ^ (-a))) →
      ∀ a : ℝ, a < c → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (g T) ((1 - γ) * (T : ℝ)),
        banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (x ^ (-a))) ∧
    -- (iii): (48) and (50) ⇒ (49) and (51), corrected
    (Tendsto (fun n : ℕ => Real.log (g ((n : ℝ) + 1)) / Real.log (g n)) atTop (𝓝 1) →
      (∀ a : ℝ, c < a → ∀ᶠ T : ℕ in atTop, ENNReal.ofReal ((T : ℝ) ^ (-a)) ≤
        banditMeasure ν π T {h | (1 - γ) * (T : ℝ) < (armPullCount i h : ℝ)}) →
      (∀ a : ℝ, a < c → ∀ᶠ T : ℕ in atTop,
        banditMeasure ν π T {h | g T < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (g T ^ (-a))) →
      ∀ a b : ℝ, a < c → c < b → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (g T) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-b)) ≤ banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} ∧
        banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (x ^ (-a))) := by
  have hg_real : Tendsto g atTop atTop := by
    have hprod := hg_log.atTop_mul_atTop₀ Real.tendsto_log_atTop
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    field_simp
  have hg_inf : Tendsto (fun T : ℕ => g T) atTop atTop := hg_real.comp tendsto_natCast_atTop_atTop
  refine ⟨fun H48 => part_i ν π i c hc γ hγ g hg_inf H48,
    fun hr H50 => part_ii ν π i c γ g hg_inf hr H50, ?_⟩
  intro hr H48 H50 a b ha hb
  filter_upwards [part_i ν π i c hc γ hγ g hg_inf H48 b hb,
    part_ii ν π i c γ g hg_inf hr H50 a ha] with T h1 h2 x hx
  exact ⟨h1 x hx, h2 x hx⟩
