-- Prove2me | solution 1 for FragileBandit.CauchyTail.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:30:11.385914+00:00
-- url     : https://prove2.me/submissions/c2480b27-97d9-409a-bdf4-7c791f06f191

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting
import Theorems.Thm_FragileBandit_CauchyTail_eq_47
import Theorems.Thm_FragileBandit_CauchyTail_lemma_5
import Theorems.Thm_FragileBandit_CauchyTail_markov_tail_bound

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTThm1Aux

/-- The mean of the family member `P^z` is `z`, so every arm mean of `ν ∈ M_P^K` lies in `I_P`. -/
lemma armMean_mem {K : ℕ} (P : Measure ℝ) (ν : StochasticBandit K) (hν : IsModelEnv P ν)
    (j : Fin K) : banditArmMean ν j ∈ meanSet P := by
  obtain ⟨z, hz, hzeq⟩ := hν j
  have hmean : banditArmMean ν j = z := by
    unfold banditArmMean
    rw [← hzeq]
    unfold expFam thetaOf
    have hz' : ∃ θ ∈ natParamSet P, Integrable id (tilt P θ) ∧ ∫ x, x ∂(tilt P θ) = z := hz
    rw [dif_pos hz']
    exact hz'.choose_spec.2.2
  rw [hmean]; exact hz

/-- Under discrimination equivalence the tail exponent of arm `k` is the number of better arms. -/
lemma tailExponent_eq_card {K : ℕ} (P : Measure ℝ) (ν : StochasticBandit K) (hν : IsModelEnv P ν)
    (hD : IsDiscEquiv P) (k : Fin K) :
    tailExponent P ν k =
      ((Finset.univ.filter (fun j => banditArmMean ν k < banditArmMean ν j)).card : ℝ≥0∞) := by
  unfold tailExponent
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
  · simp
  · intro j hj
    exact hD _ (armMean_mem P ν hν j) _ (armMean_mem P ν hν k) (Finset.mem_filter.1 hj).2

/-- (7) on a general window `[g(T), (1-γ)T]`, from (47) and Lemma 5 (i). -/
lemma lower_on_window {K : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (π : BanditPolicy K) (hπ : IsOptimized P π)
    (ν : StochasticBandit K) (hν : IsModelEnv P ν) (hd : DistinctMeans ν) (k : Fin K)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (g : ℝ → ℝ) (hg_mono : StrictMonoOn g (Set.Ioi 1)) (hg_pos : ∀ t : ℝ, 1 < t → 0 < g t)
    (hg_log : Tendsto (fun t : ℝ => g t / Real.log t) atTop atTop)
    (hg_o : Tendsto (fun t : ℝ => g t / t) atTop (𝓝 0)) :
    ∀ a : ℝ, tailExponent P ν k < ENNReal.ofReal a → ∀ᶠ T : ℕ in atTop,
      ∀ x ∈ Set.Icc (g T) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-a)) ≤ banditMeasure ν π T {h | x < (armPullCount k h : ℝ)} := by
  intro a ha
  have hne : tailExponent P ν k ≠ ⊤ := ne_top_of_lt ha
  set t : ℝ := (tailExponent P ν k).toReal with ht
  have hteq : tailExponent P ν k = ENNReal.ofReal t := (ENNReal.ofReal_toReal hne).symm
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  rw [hteq] at ha
  have hta : t < a := by
    by_contra hcon; push_neg at hcon
    exact absurd ha (not_lt.2 (ENNReal.ofReal_le_ofReal hcon))
  set c : ℝ := (t + a) / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hca : c < a := by rw [hc]; linarith
  have H48 : ∀ a' : ℝ, c < a' → ∀ᶠ T : ℕ in atTop, ENNReal.ofReal ((T : ℝ) ^ (-a')) ≤
      banditMeasure ν π T {h | (1 - γ) * (T : ℝ) < (armPullCount k h : ℝ)} := by
    intro a' ha'
    apply eq_47 P hP π hπ ν hν hd k γ hγ a'
    rw [hteq]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by rw [hc] at ha'; linarith)
  exact (lemma_5 ν π k c hcpos γ hγ g hg_mono hg_pos hg_log hg_o).1 H48 a hca

lemma g_log_props (γ : ℝ) (hγ : 0 < γ) :
    StrictMonoOn (fun t : ℝ => Real.log t ^ (1 + γ)) (Set.Ioi 1) ∧
    (∀ t : ℝ, 1 < t → 0 < Real.log t ^ (1 + γ)) ∧
    Tendsto (fun t : ℝ => Real.log t ^ (1 + γ) / Real.log t) atTop atTop ∧
    Tendsto (fun t : ℝ => Real.log t ^ (1 + γ) / t) atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    have hs' : 0 < Real.log s := Real.log_pos hs
    exact Real.rpow_lt_rpow hs'.le (Real.log_lt_log (by linarith [hs.out]) hst) (by linarith)
  · intro t ht
    exact Real.rpow_pos_of_pos (Real.log_pos ht) _
  · have h := (tendsto_rpow_atTop hγ).comp Real.tendsto_log_atTop
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have hl : 0 < Real.log t := Real.log_pos ht
    simp only [Function.comp]
    rw [Real.rpow_add hl, Real.rpow_one]
    field_simp
  · have h := (isLittleO_log_rpow_rpow_atTop (1 + γ) one_pos).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.rpow_one]

lemma g_pow_props (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    StrictMonoOn (fun t : ℝ => t ^ γ) (Set.Ioi 1) ∧
    (∀ t : ℝ, 1 < t → 0 < t ^ γ) ∧
    Tendsto (fun t : ℝ => t ^ γ / Real.log t) atTop atTop ∧
    Tendsto (fun t : ℝ => t ^ γ / t) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => Real.log (((n : ℝ) + 1) ^ γ) / Real.log ((n : ℝ) ^ γ)) atTop (𝓝 1) := by
  obtain ⟨hγ0, hγ1⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    exact Real.rpow_lt_rpow (by linarith [hs.out]) hst hγ0
  · intro t ht
    exact Real.rpow_pos_of_pos (by linarith) _
  · have h0 := (isLittleO_log_rpow_atTop hγ0).tendsto_div_nhds_zero
    have h1 : Tendsto (fun t : ℝ => Real.log t / t ^ γ) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨h0, ?_⟩
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      exact div_pos (Real.log_pos ht) (Real.rpow_pos_of_pos (by linarith) _)
    have h2 := tendsto_inv_nhdsGT_zero.comp h1
    refine h2.congr' ?_
    filter_upwards with t
    simp [Function.comp, inv_div]
  · have h := tendsto_rpow_neg_atTop (y := 1 - γ) (by linarith)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [show -(1 - γ) = γ - 1 by ring, Real.rpow_sub ht, Real.rpow_one]
  · have hdiff := Real.tendsto_log_nat_add_one_sub_log
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h := (hdiff.div_atTop hlog).const_add 1
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    rw [Real.log_rpow (by linarith), Real.log_rpow (by linarith)]
    field_simp
    ring

end CTThm1Aux

open CTThm1Aux in
theorem solution {K : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (π : BanditPolicy K) (hπ : IsOptimized P π)
    (ν : StochasticBandit K) (hν : IsModelEnv P ν) (hd : DistinctMeans ν) (k : Fin K)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    -- (7)
    (∀ a : ℝ, tailExponent P ν k < ENNReal.ofReal a → ∀ᶠ T : ℕ in atTop,
      ∀ x ∈ Set.Icc (Real.log T ^ (1 + γ)) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-a)) ≤ banditMeasure ν π T {h | x < (armPullCount k h : ℝ)}) ∧
    -- (8)
    (IsDiscEquiv P →
      (Finset.univ.filter (fun j => banditArmMean ν k < banditArmMean ν j)).card = 1 →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc ((T : ℝ) ^ γ) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-(1 + ε))) ≤ banditMeasure ν π T {h | x < (armPullCount k h : ℝ)} ∧
        banditMeasure ν π T {h | x < (armPullCount k h : ℝ)} ≤ ENNReal.ofReal (x ^ (-(1 - ε)))) ∧
    -- (7) with right side −(i − 1)
    (IsDiscEquiv P →
      ∀ a : ℝ, ((Finset.univ.filter (fun j => banditArmMean ν k < banditArmMean ν j)).card : ℝ) < a →
      ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (Real.log T ^ (1 + γ)) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-a)) ≤ banditMeasure ν π T {h | x < (armPullCount k h : ℝ)}) := by
  obtain ⟨gl1, gl2, gl3, gl4⟩ := g_log_props γ hγ.1
  obtain ⟨gp1, gp2, gp3, gp4, gp5⟩ := g_pow_props γ hγ
  have H7 := lower_on_window P hP π hπ ν hν hd k γ hγ _ gl1 gl2 gl3 gl4
  refine ⟨H7, ?_, ?_⟩
  · intro hD hcard ε hε
    -- lower bound: tail exponent is 1
    have hte : tailExponent P ν k = 1 := by
      rw [tailExponent_eq_card P ν hν hD k, hcard]; simp
    have hlow := lower_on_window P hP π hπ ν hν hd k γ hγ _ gp1 gp2 gp3 gp4 (1 + ε)
      (by rw [hte, ← ENNReal.ofReal_one]
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
    -- upper bound: Markov + Lemma 5 (ii)
    have hgap : 0 < banditGap ν k := by
      obtain ⟨j, hj⟩ : (Finset.univ.filter
          (fun j => banditArmMean ν k < banditArmMean ν j)).Nonempty := by
        rw [← Finset.card_pos, hcard]; exact one_pos
      have hjlt := (Finset.mem_filter.1 hj).2
      have hle : banditArmMean ν j ≤ banditOptimalMean ν :=
        le_ciSup (Set.finite_range _).bddAbove j
      unfold banditGap; linarith
    have H50 : ∀ a : ℝ, a < 1 → ∀ᶠ T : ℕ in atTop,
        banditMeasure ν π T {h | (fun t : ℝ => t ^ γ) T < (armPullCount k h : ℝ)} ≤
          ENNReal.ofReal ((fun t : ℝ => t ^ γ) T ^ (-a)) := by
      intro a ha
      have := markov_tail_bound P hP π hπ ν hν hd k hgap γ ⟨hγ.1, hγ.2.le⟩ 1 one_pos a ha
      simpa only [one_mul] using this
    have hup := (lemma_5 ν π k 1 one_pos γ hγ _ gp1 gp2 gp3 gp4).2.1 gp5 H50 (1 - ε)
      (by linarith)
    filter_upwards [hlow, hup] with T h1 h2 x hx
    exact ⟨h1 x hx, h2 x hx⟩
  · intro hD a ha
    apply H7 a
    rw [tailExponent_eq_card P ν hν hD k, ← ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (Nat.cast_nonneg _) ha)).2 ha
