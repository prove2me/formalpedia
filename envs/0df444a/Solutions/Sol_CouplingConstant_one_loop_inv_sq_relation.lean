-- Prove2me | solution 1 for CouplingConstant.one_loop_inv_sq_relation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T20:09:30.121016+00:00
-- url     : https://prove2.me/submissions/718eaec2-5b52-4163-9d6d-abc821087857

import Mathlib
import Definitions.Def_CouplingConstantDefs

open CouplingConstant Filter Topology

theorem W2p_CouplingConstant_alphaOneLoop_decreasing_tendsto_zero (beta0 Lam : ℝ)
    (hbeta : 0 < beta0)
    (hLam : 0 < Lam) :
    (∀ Q1 Q2 : ℝ, Lam < Q1 → Q1 < Q2 →
        alphaOneLoop beta0 Lam Q2 < alphaOneLoop beta0 Lam Q1) ∧
      Filter.Tendsto (alphaOneLoop beta0 Lam) Filter.atTop (nhds 0) := by
  refine ⟨fun Q1 Q2 h1 h2 => ?_, ?_⟩
  · have hQ1 : 0 < Q1 := by linarith
    have hL1 : 0 < Real.log (Q1 ^ 2 / Lam ^ 2) :=
      Real.log_pos (by rw [one_lt_div (by positivity)]; nlinarith)
    have hL12 : Real.log (Q1 ^ 2 / Lam ^ 2) < Real.log (Q2 ^ 2 / Lam ^ 2) :=
      Real.log_lt_log (by positivity) (div_lt_div_of_pos_right (by nlinarith) (by positivity))
    unfold alphaOneLoop
    exact one_div_lt_one_div_of_lt (mul_pos hbeta hL1) (mul_lt_mul_of_pos_left hL12 hbeta)
  · have h1 : Tendsto (fun Q : ℝ => Q ^ 2 / Lam ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const (by positivity)
    have h2 := (Real.tendsto_log_atTop.comp h1).const_mul_atTop hbeta
    exact Filter.Tendsto.congr (fun Q => by simp [alphaOneLoop, Function.comp_def])
      (tendsto_inv_atTop_zero.comp h2)

theorem W2p_CouplingConstant_alphaOneLoop_hasDerivAt (beta0 Lam Q : ℝ) (hbeta : 0 < beta0)
    (hLam : 0 < Lam)
    (hQ : Lam < Q) :
    HasDerivAt (alphaOneLoop beta0 Lam)
      (-(2 / Q) * beta0 * (alphaOneLoop beta0 Lam Q) ^ 2) Q := by
  have hQ0 : 0 < Q := by linarith
  have hL : 0 < Real.log (Q ^ 2 / Lam ^ 2) :=
    Real.log_pos (by rw [one_lt_div (by positivity)]; nlinarith)
  have h1 : HasDerivAt (fun x => x ^ 2 / Lam ^ 2) (2 * Q / Lam ^ 2) Q := by
    simpa using (hasDerivAt_pow 2 Q).div_const (Lam ^ 2)
  have h2 := ((h1.log (by positivity : Q ^ 2 / Lam ^ 2 ≠ 0)).const_mul beta0).inv
    ((mul_pos hbeta hL).ne' : beta0 * Real.log (Q ^ 2 / Lam ^ 2) ≠ 0)
  have e : alphaOneLoop beta0 Lam = fun x => (beta0 * Real.log (x ^ 2 / Lam ^ 2))⁻¹ := by
    funext x; simp [alphaOneLoop]
  have hQ0' := hQ0.ne'
  have hLam' := hLam.ne'
  have hb' := hbeta.ne'
  have hL' := hL.ne'
  have key : -(2 / Q) * beta0 * (alphaOneLoop beta0 Lam Q) ^ 2 =
      -(beta0 * (2 * Q / Lam ^ 2 / (Q ^ 2 / Lam ^ 2))) / (beta0 * Real.log (Q ^ 2 / Lam ^ 2)) ^ 2 := by
    unfold alphaOneLoop
    field_simp
  rw [key, e]
  exact h2

theorem W2p_CouplingConstant_beta_vanishes_scale_invariant (g : ℝ → ℝ)
    (hg : IsOneLoopRunning 0 g Set.univ) (t : ℝ) :
    g t = g 0 := by
  have hd : ∀ t, HasDerivAt g 0 t := fun t => by
    simpa [betaOneLoop] using hg t (Set.mem_univ t)
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0

theorem solution (b g0 T : ℝ) (g : ℝ → ℝ) (hg0 : 0 < g0)
    (h0 : g 0 = g0)
    (hT : 0 ≤ T) (hg : IsOneLoopRunning b g (Set.Icc 0 T)) :
    ∀ t ∈ Set.Icc 0 T, (g t) ^ 2 * (1 - 2 * b * g0 ^ 2 * t) = g0 ^ 2 := by
  intro t ht
  have hcont : ContinuousOn g (Set.Icc 0 T) :=
    fun s hs => (hg s hs).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hcont
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = fun s => g s * g s * (1 - 2 * b * g0 ^ 2 * s) - g0 ^ 2 :=
    ⟨_, rfl⟩
  have hGd : ∀ s ∈ Set.Icc 0 T, HasDerivAt G (2 * b * (g s * g s) * G s) s := by
    intro s hs
    have h1 := hg s hs
    have h2 : HasDerivAt (fun s => 1 - 2 * b * g0 ^ 2 * s) (-(2 * b * g0 ^ 2)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * b * g0 ^ 2)).const_sub 1
    have h3 := ((h1.mul h1).mul h2).sub_const (g0 ^ 2)
    rw [hGdef]
    exact h3.congr_deriv (by simp only [betaOneLoop, Pi.mul_apply]; ring)
  have hGc : ContinuousOn G (Set.Icc 0 T) :=
    fun s hs => (hGd s hs).continuousAt.continuousWithinAt
  have hGw : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt G (2 * b * (g s * g s) * G s) (Set.Ici s) s :=
    fun s hs => (hGd s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
  have hG0 : G 0 = 0 := by
    rw [hGdef]
    show g 0 * g 0 * (1 - 2 * b * g0 ^ 2 * 0) - g0 ^ 2 = 0
    rw [h0]; ring
  have hbound : ∀ s ∈ Set.Ico 0 T,
      ‖2 * b * (g s * g s) * G s‖ ≤ (2 * |b| * (C * C)) * ‖G s‖ := by
    intro s hs
    have hgs := hC s (Set.Ico_subset_Icc_self hs)
    rw [Real.norm_eq_abs] at hgs
    simp only [Real.norm_eq_abs, abs_mul, abs_two]
    have hgg : |g s| * |g s| ≤ C * C :=
      mul_le_mul hgs hgs (abs_nonneg _) ((abs_nonneg _).trans hgs)
    have := mul_le_mul_of_nonneg_left hgg
      (by positivity : (0 : ℝ) ≤ 2 * |b| * |G s|)
    nlinarith [this]
  have hz : g t * g t * (1 - 2 * b * g0 ^ 2 * t) - g0 ^ 2 = 0 := by
    have := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hGc hGw hG0 hbound t ht
    rw [hGdef] at this
    exact this
  linear_combination hz

theorem W2p_CouplingConstant_one_loop_pos (b g0 T : ℝ) (g : ℝ → ℝ) (hg0 : 0 < g0)
    (h0 : g 0 = g0)
    (hT : 0 ≤ T) (hg : IsOneLoopRunning b g (Set.Icc 0 T)) :
    ∀ t ∈ Set.Icc 0 T, 0 < g t := by
  intro t ht
  have hrel := solution b g0 T g hg0 h0 hT hg
  by_contra hneg
  push_neg at hneg
  have hcont : ContinuousOn g (Set.Icc 0 t) :=
    fun s hs => (hg s ⟨hs.1, hs.2.trans ht.2⟩).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc' ht.1 hcont ⟨hneg, by rw [h0]; exact hg0.le⟩
  have h1 := hrel s ⟨hs.1, hs.2.trans ht.2⟩
  rw [hgs] at h1
  have h2 : g0 ^ 2 = 0 := by rw [← h1]; ring
  have h3 : 0 < g0 ^ 2 := by positivity
  linarith

theorem W2p_CouplingConstant_landau_pole (b g0 : ℝ) (hb : 0 < b) (hg0 : 0 < g0) :
    ¬ ∃ g : ℝ → ℝ, g 0 = g0 ∧
      IsOneLoopRunning b g (Set.Icc 0 (1 / (2 * b * g0 ^ 2))) := by
  rintro ⟨g, h0, hg⟩
  have hT : 0 ≤ 1 / (2 * b * g0 ^ 2) := by positivity
  have h1 := solution b g0 _ g hg0 h0 hT hg
    (1 / (2 * b * g0 ^ 2)) ⟨hT, le_rfl⟩
  rw [mul_one_div_cancel (by positivity), sub_self, mul_zero] at h1
  have h3 : 0 < g0 ^ 2 := by positivity
  linarith

theorem W2p_CouplingConstant_asymptotic_freedom_limit (b g0 : ℝ) (g : ℝ → ℝ) (hb : b < 0)
    (hg0 : 0 < g0)
    (h0 : g 0 = g0) (hg : IsOneLoopRunning b g (Set.Ici 0)) :
    Filter.Tendsto g Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun t => (2 * (-b) * t) * (g t) ^ 2) Filter.atTop (nhds 1) := by
  have hsub : ∀ t, 0 ≤ t → IsOneLoopRunning b g (Set.Icc 0 t) :=
    fun t _ s hs => hg s (Set.mem_Ici.mpr hs.1)
  have hrel : ∀ t, 0 ≤ t → g t ^ 2 * (1 - 2 * b * g0 ^ 2 * t) = g0 ^ 2 := fun t ht =>
    solution b g0 t g hg0 h0 ht (hsub t ht) t ⟨ht, le_rfl⟩
  have hpos : ∀ t, 0 ≤ t → 0 < g t := fun t ht =>
    W2p_CouplingConstant_one_loop_pos b g0 t g hg0 h0 ht (hsub t ht) t ⟨ht, le_rfl⟩
  have hg2 : 0 < g0 ^ 2 := by positivity
  have hk : 0 < -2 * b * g0 ^ 2 := by nlinarith
  have hD : ∀ t, 0 ≤ t → 0 < 1 - 2 * b * g0 ^ 2 * t := by
    intro t ht; nlinarith [mul_nonneg hk.le ht]
  have hgt : ∀ t, 0 ≤ t → g t ^ 2 = g0 ^ 2 / (1 - 2 * b * g0 ^ 2 * t) := fun t ht =>
    (eq_div_iff (hD t ht).ne').mpr (hrel t ht)
  have hden : Tendsto (fun t => 1 - 2 * b * g0 ^ 2 * t) atTop atTop := by
    have := tendsto_atTop_add_const_left atTop 1 (tendsto_id.const_mul_atTop hk)
    exact this.congr (fun t => by simp only [id]; ring)
  constructor
  · have hq : Tendsto (fun t => g0 ^ 2 / (1 - 2 * b * g0 ^ 2 * t)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have hs := (Real.continuous_sqrt.tendsto 0).comp hq
    rw [Real.sqrt_zero] at hs
    refine hs.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Function.comp]
    rw [← hgt t ht, Real.sqrt_sq (hpos t ht).le]
  · have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden)
    rw [sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := (hD t ht).ne'
    rw [hgt t ht]
    field_simp <;> ring

theorem W2p_CouplingConstant_running_coupling_dichotomy (b g0 : ℝ) (hg0 : 0 < g0) :
    (b < 0 → ∀ g : ℝ → ℝ, g 0 = g0 → IsOneLoopRunning b g (Set.Ici 0) →
        Filter.Tendsto g Filter.atTop (nhds 0) ∧
          Filter.Tendsto (fun t => (2 * (-b) * t) * (g t) ^ 2) Filter.atTop (nhds 1)) ∧
      (0 < b → ¬ ∃ g : ℝ → ℝ, g 0 = g0 ∧
        IsOneLoopRunning b g (Set.Icc 0 (1 / (2 * b * g0 ^ 2)))) :=
  ⟨fun hb g h0 hg => W2p_CouplingConstant_asymptotic_freedom_limit b g0 g hb hg0 h0 hg,
    fun hb => W2p_CouplingConstant_landau_pole b g0 hb hg0⟩
