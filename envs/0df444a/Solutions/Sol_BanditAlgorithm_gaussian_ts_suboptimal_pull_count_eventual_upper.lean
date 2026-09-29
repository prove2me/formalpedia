-- Prove2me | solution 1 for BanditAlgorithm.gaussian_ts_suboptimal_pull_count_eventual_upper
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T02:11:11.692424+00:00
-- url     : https://prove2.me/submissions/097eea5e-7925-4388-9a0e-e00c2c898edc

import Theorems.Thm_BanditAlgorithm_thompson_sampling_pull_count_bound_exact_ranks
import Theorems.Thm_BanditAlgorithm_gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_uniform
import Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_exact_rank_overshoot_sum_sharp
import Mathlib.Analysis.SpecialFunctions.CompareExp
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory ENNReal Filter Topology

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator_upper {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) :
    (armPullCount i h : ℝ) = ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by
    ext t
    simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
      Finset.univ).symm

private theorem measurable_armPullCount_cast_upper {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then 1 else 0 by
    funext h
    exact pullCount_cast_eq_sum_indicator_upper i h]
  apply Finset.measurable_sum
  intro t _
  exact Measurable.ite
    ((measurableSet_singleton i).preimage
      (measurable_fst.comp (measurable_pi_apply t)))
    measurable_const measurable_const

private theorem armPullCount_le_horizon_upper {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) : armPullCount i h ≤ n := by
  change ({t | (h t).1 = i}.toFinset : Finset (Fin n)).card ≤ n
  simpa using
    (Finset.card_le_univ
      ({t | (h t).1 = i}.toFinset : Finset (Fin n)))

private theorem integrable_armPullCount_upper {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact (measurable_armPullCount_cast_upper i).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦ by
      constructor
      · positivity
      · exact_mod_cast armPullCount_le_horizon_upper i h

private theorem tendsto_log_nat_upper :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_inv_log_nat_upper :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_nat_upper

private theorem tendsto_sqrt_log_nat_upper :
    Tendsto (fun n : ℕ ↦ Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_log_nat_upper

private theorem tendsto_inv_sqrt_log_nat_upper :
    Tendsto (fun n : ℕ ↦
      (Real.sqrt (Real.log (n : ℝ)))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_sqrt_log_nat_upper

private theorem tendsto_sqrt_pi_log_div_log_upper :
    Tendsto
      (fun n : ℕ ↦
        Real.sqrt (Real.pi * Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hprod :
      Tendsto
        (fun n : ℕ ↦ Real.sqrt Real.pi *
          (Real.sqrt (Real.log (n : ℝ)))⁻¹)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds (x := Real.sqrt Real.pi)).mul
        tendsto_inv_sqrt_log_nat_upper
  refine hprod.congr' ?_
  filter_upwards [tendsto_log_nat_upper.eventually_gt_atTop 0] with n hn
  rw [Real.sqrt_mul (le_of_lt Real.pi_pos), mul_div_assoc,
    Real.sqrt_div_self]

private theorem exists_positive_offset_upper {Δ b : ℝ}
    (hΔ : 0 < Δ) (hb : 2 / Δ ^ 2 < b) :
    ∃ ε : ℝ, 0 < ε ∧ ε < Δ ∧ 2 / (Δ - ε) ^ 2 < b := by
  have hcont :
      Tendsto (fun ε : ℝ ↦ 2 / (Δ - ε) ^ 2)
        (𝓝 0) (𝓝 (2 / Δ ^ 2)) := by
    have hsub :
        Tendsto (fun ε : ℝ ↦ Δ - ε) (𝓝 0) (𝓝 Δ) := by
      simpa using
        (tendsto_const_nhds (x := Δ)).sub
          (tendsto_id : Tendsto (fun ε : ℝ ↦ ε) (𝓝 0) (𝓝 0))
    have hinv := (hsub.pow 2).inv₀ (pow_ne_zero 2 (ne_of_gt hΔ))
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul hinv
  have hcoef : ∀ᶠ ε : ℝ in 𝓝 0, 2 / (Δ - ε) ^ 2 < b :=
    hcont.eventually (eventually_lt_nhds hb)
  have hcoef' : ∀ᶠ ε : ℝ in 𝓝[>] 0, 2 / (Δ - ε) ^ 2 < b :=
    hcoef.filter_mono inf_le_left
  have hlt' : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < Δ :=
    (eventually_lt_nhds hΔ).filter_mono inf_le_left
  have hpos' : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε :=
    self_mem_nhdsWithin
  rcases (hcoef'.and (hlt'.and hpos')).exists with
    ⟨ε, hcoefε, hltε, hposε⟩
  exact ⟨ε, hposε, hltε, hcoefε⟩

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k : ℕ} [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k)
    (hπ : IsGaussianTSPolicy π) (i : Fin k)
    (hi : 0 < banditGap (gaussianBandit μvec) i) :
    ∀ b : ℝ, 2 / banditGap (gaussianBandit μvec) i ^ 2 < b →
      ∀ᶠ n : ℕ in Filter.atTop,
        (∫ h, (armPullCount i h : ℝ)
          ∂banditMeasure (gaussianBandit μvec) π n) /
            Real.log n < b := by
  intro b hb
  let ν := gaussianBandit μvec
  let Δ : ℝ := banditGap ν i
  have hΔ : 0 < Δ := by simpa [Δ, ν] using hi
  obtain ⟨ε, hε, hεΔ, hcoeff⟩ :=
    exists_positive_offset_upper hΔ (by simpa [Δ, ν] using hb)
  let e : ℝ := Δ - ε
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨C, hC, hoptSum⟩ :=
    gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_uniform
  let K : ℝ :=
    2 * Real.exp (ε ^ 2 / 8) / (ε ^ 2 / 8) +
      (2 * C / ε ^ 2) *
        (Real.exp (3 * ε ^ 2 / 32) / (3 * ε ^ 2 / 32))
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ (banditArmMean ν)
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  have hopt : banditArmMean ν i₀ = banditOptimalMean ν := by
    apply le_antisymm
    · exact le_ciSup
        (Finite.bddAbove_range (fun j ↦ banditArmMean ν j)) i₀
    · unfold banditOptimalMean
      exact ciSup_le fun j ↦ hi₀ j (Finset.mem_univ j)
  have hine : i ≠ i₀ := by
    intro hieq
    subst i
    have hzero : banditGap ν i₀ = 0 := by
      rw [banditGap, hopt]
      ring
    have : Δ = 0 := by simpa [Δ] using hzero
    linarith
  let R : ℕ → ℝ := fun n ↦
    (2 + K + 2 / e ^ 2 *
      (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1)) /
        Real.log n
  have hR : Tendsto R atTop (𝓝 (2 / e ^ 2)) := by
    have hzero₁ :
        Tendsto (fun n : ℕ ↦
          (2 + K + 2 / e ^ 2) * (Real.log (n : ℝ))⁻¹)
          atTop (𝓝 0) := by
      simpa using
        (tendsto_const_nhds (x := 2 + K + 2 / e ^ 2)).mul
          tendsto_inv_log_nat_upper
    have hzero₂ :
        Tendsto (fun n : ℕ ↦
          (2 / e ^ 2) *
            (Real.sqrt (Real.pi * Real.log (n : ℝ)) /
              Real.log (n : ℝ)))
          atTop (𝓝 0) := by
      simpa using
        (tendsto_const_nhds (x := 2 / e ^ 2)).mul
          tendsto_sqrt_pi_log_div_log_upper
    have hsum :=
      (hzero₁.add (tendsto_const_nhds (x := 2 / e ^ 2))).add hzero₂
    have hsum' :
        Tendsto
          (fun n : ℕ ↦
            (2 + K + 2 / e ^ 2) * (Real.log (n : ℝ))⁻¹ +
              2 / e ^ 2 +
              (2 / e ^ 2) *
                (Real.sqrt (Real.pi * Real.log (n : ℝ)) /
                  Real.log (n : ℝ)))
          atTop (𝓝 (2 / e ^ 2)) := by
      simpa only [zero_add, add_zero] using hsum
    refine hsum'.congr' ?_
    filter_upwards [tendsto_log_nat_upper.eventually_gt_atTop 0] with n hn
    dsimp [R]
    field_simp [ne_of_gt hn]
    ring
  have hRlt : ∀ᶠ n : ℕ in atTop, R n < b :=
    hR.eventually (eventually_lt_nhds (by simpa [e] using hcoeff))
  filter_upwards [hRlt, eventually_atTop.2 ⟨2, fun n hn ↦ hn⟩,
    tendsto_log_nat_upper.eventually_gt_atTop 0] with n hRn hn hlog
  have hoptN :
      (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i₀ h),
          ENNReal.ofReal
            (1 / gaussianTSTailProb i₀ s
              (banditArmMean ν i₀ - ε) h - 1)
          ∂banditMeasure ν π n) ≤ ENNReal.ofReal K := by
    simpa [K, ν] using
      hoptSum k μvec π i₀ (by simpa [ν] using hopt) ε hε n
  have hsubN :
      (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
          (if 1 / (n : ℝ) <
              gaussianTSTailProb i s (banditArmMean ν i₀ - ε) h
            then (1 : ℝ≥0∞) else 0)
          ∂banditMeasure ν π n) ≤
        ENNReal.ofReal
          (1 + 2 / e ^ 2 *
            (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1)) := by
    simpa [e, Δ, ν] using
      gaussian_ts_suboptimal_exact_rank_overshoot_sum_sharp
        k μvec π i₀ (by simpa [ν] using hopt) i hi ε hε
          (by simpa [Δ, ν] using hεΔ) n hn
  have hdecomp :=
    thompson_sampling_pull_count_bound_exact_ranks
      ν hπ i₀ hopt i hine ε n
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := hlog.le
  have hsubArg :
      0 ≤ 1 + 2 / e ^ 2 *
        (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1) := by
    positivity
  have hlin :
      (∫⁻ h, (armPullCount i h : ℝ≥0∞)
        ∂banditMeasure ν π n) ≤
          ENNReal.ofReal
            (2 + K + 2 / e ^ 2 *
              (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1)) := by
    apply hdecomp.trans
    calc
      1 + (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i₀ h),
            ENNReal.ofReal
              (1 / gaussianTSTailProb i₀ s
                (banditArmMean ν i₀ - ε) h - 1)
            ∂banditMeasure ν π n)
          + (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
            (if 1 / (n : ℝ) <
                gaussianTSTailProb i s (banditArmMean ν i₀ - ε) h
              then (1 : ℝ≥0∞) else 0)
            ∂banditMeasure ν π n) ≤
          1 + ENNReal.ofReal K + ENNReal.ofReal
            (1 + 2 / e ^ 2 *
              (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1)) := by
        gcongr
      _ = ENNReal.ofReal
          (2 + K + 2 / e ^ 2 *
            (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1)) := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
          ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1) hK,
          ← ENNReal.ofReal_add
            (add_nonneg (by positivity : (0 : ℝ) ≤ 1) hK) hsubArg]
        congr 1
        ring
  have hInt := integrable_armPullCount_upper (n := n) ν π i
  have hof :
      ENNReal.ofReal
          (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) =
        ∫⁻ h, (armPullCount i h : ℝ≥0∞) ∂banditMeasure ν π n := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun h ↦ by positivity)]
    apply lintegral_congr
    intro h
    simp
  have harg :
      0 ≤ 2 + K + 2 / e ^ 2 *
        (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1) := by
    positivity
  have hreal :
      (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) ≤
        2 + K + 2 / e ^ 2 *
          (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1) := by
    apply (ENNReal.ofReal_le_ofReal_iff harg).mp
    rw [hof]
    exact hlin
  calc
    (∫ h, (armPullCount i h : ℝ)
        ∂banditMeasure (gaussianBandit μvec) π n) / Real.log n ≤
        R n := by
      dsimp [R, ν] at hreal ⊢
      exact div_le_div_of_nonneg_right hreal hlog.le
    _ < b := hRn
