-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_bounded_stop_positive_time_ito_stieltjes_of_reserve_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:04:00.396145+00:00
-- url     : https://prove2.me/submissions/ae389055-08df-455e-a8b4-05c92a6666f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_positive_stieltjes_left_grid_L1_consistency
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 800000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (v : ℝ → ℝ) (a b l u : ℝ) (hal : a < l) (hub : u < b)
    (hv : ContDiffOn ℝ 2 v (Ioo a b))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (T : ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hBound : ∀ ω, ρ ω ≤ T)
    (hInitial : ∀ ω, x - rightLimit D 0 ω ∈ Icc l u)
    (hActive : ∀ ω t, 0 < t → t < ρ ω →
      riskProcess X x D t ω ∈ Icc l u ∧
      (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) ∈ Icc l u)
    (hTerminal : ∀ᵐ ω ∂P, 0 < ρ ω → riskProcess X x D (ρ ω) ω ∈ Icc l u) :
  let pre : ℝ≥0 → Ω → ℝ := riskProcess X x D
  let jump : ℝ≥0 → Ω → ℝ := fun t ω => rightLimit D t ω - D t ω
  let post : ℝ≥0 → Ω → ℝ := fun t ω => pre t ω - jump t ω
  let toll : Ω → ℝ → ℝ := fun ω s =>
    if jump s.toNNReal ω = 0 then deriv v (pre s.toNNReal ω)
    else (v (pre s.toNNReal ω) - v (post s.toNNReal ω)) / jump s.toNNReal ω
  let paid : Ω → ℝ → ℝ := fun ω s => Real.exp (-(q * s)) * toll ω s
  let finish : Ω → ℝ := fun ω =>
    if ρ ω = 0 then post (ρ ω) ω else pre (ρ ω) ω
  let driftTerm : Ω → ℝ → ℝ := fun ω s =>
    Real.exp (-(q * s)) * (X.generator v (pre s.toNNReal ω) - q * v (pre s.toNNReal ω))
  ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
    ∀ᵐ ω ∂P, IntegrableOn (paid ω) (Ioo (0 : ℝ) (ρ ω : ℝ)) (dividendMeasure D ω) ∧
      Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) +
          (∫ s in Ioo (0 : ℝ) (ρ ω : ℝ), paid ω s ∂(dividendMeasure D ω)) =
        v (post 0 ω) + M ω + (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  letI : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  let pre : ℝ≥0 → Ω → ℝ := riskProcess X x D
  let jump : ℝ≥0 → Ω → ℝ := fun t ω => rightLimit D t ω - D t ω
  let post : ℝ≥0 → Ω → ℝ := fun t ω => pre t ω - jump t ω
  let toll : Ω → ℝ → ℝ := fun ω s =>
    if jump s.toNNReal ω = 0 then deriv v (pre s.toNNReal ω)
    else (v (pre s.toNNReal ω) - v (post s.toNNReal ω)) / jump s.toNNReal ω
  let paid : Ω → ℝ → ℝ := fun ω s => Real.exp (-(q * s)) * toll ω s
  let finish : Ω → ℝ := fun ω =>
    if ρ ω = 0 then post (ρ ω) ω else pre (ρ ω) ω
  let driftTerm : Ω → ℝ → ℝ := fun ω s =>
    Real.exp (-(q * s)) * (X.generator v (pre s.toNNReal ω) - q * v (pre s.toNNReal ω))
  let clamp : ℝ → ℝ := fun y => max l (min u y)
  let R : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let step : ℕ → ℝ≥0 := fun j => T / ((j + 1 : ℕ) : ℝ≥0)
  let left : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * step j
  let weight : ℕ → ℕ → Ω → ℝ := fun j i ω =>
    if ρ ω ≤ left j i then 0 else
      Real.exp (-(q * (left j i : ℝ))) * deriv v (clamp (post (left j i) ω))
  let S : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range (j + 1),
    weight j i ω * (R (left j i + step j) ω - R (left j i) ω)
  let residual : Ω → ℝ := fun ω =>
    (Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) +
      (∫ s in Ioo (0 : ℝ) (ρ ω : ℝ), paid ω s ∂(dividendMeasure D ω))) -
        v (post 0 ω) - (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s)
  have hlu : l ≤ u := (hInitial Classical.ofNonempty).1.trans (hInitial Classical.ofNonempty).2
  have hInterval : Icc l u ⊆ Ioo a b := fun y hy =>
    ⟨hal.trans_le hy.1, hy.2.trans_lt hub⟩
  have hClampIn (y : ℝ) : clamp y ∈ Icc l u :=
    ⟨le_max_left _ _, max_le hlu (min_le_left _ _)⟩
  have hClampEq (y : ℝ) (hy : y ∈ Icc l u) : clamp y = y := by
    simp [clamp, min_eq_right hy.2, max_eq_right hy.1]
  have hClampC : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hDerC : ContinuousOn (deriv v) (Ioo a b) :=
    hv.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hVClamp : Continuous (fun y => v (clamp y)) :=
    hv.continuousOn.comp_continuous hClampC (fun y => hInterval (hClampIn y))
  have hDerClamp : Continuous (fun y => deriv v (clamp y)) :=
    hDerC.comp_continuous hClampC (fun y => hInterval (hClampIn y))
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.bddAbove_image (hDerC.mono hInterval).norm
  let K : ℝ := max 0 K₀
  have hK : 0 ≤ K := le_max_left _ _
  have hDerivativeBound (y : ℝ) (hy : y ∈ Icc l u) : ‖deriv v y‖ ≤ K :=
    (hK₀ ⟨y, hy, rfl⟩).trans (le_max_right _ _)
  have hDiscount (s : ℝ) (hs : 0 ≤ s) (hsT : s ≤ (T : ℝ)) :
      Real.exp (-(q * s)) ≤ Real.exp (|q| * (T : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [← neg_mul]
    exact (mul_le_mul_of_nonneg_right (neg_le_abs q) hs).trans
      (mul_le_mul_of_nonneg_left hsT (abs_nonneg q))
  have hS (j : ℕ) : Integrable (S j) P ∧ (∫ ω, S j ω ∂P) = 0 := by
    have hMart : Martingale R 𝓕.rightCont P :=
      avram_wave6_03_original_rightCont_zerojump_centered_source_martingale X hν
    refine avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
      (Finset.range (j + 1)) R hMart.integrable (fun _ _ h => hMart.condExp_ae_eq h)
      (left j) (fun i => left j i + step j) (weight j) ?_ ?_ (Real.exp (|q| * (T : ℝ)) * K) ?_
    · intro i _
      exact le_add_of_nonneg_right (by positivity)
    · intro i _
      let s := left j i
      have hXmeas : Measurable[𝓕.rightCont s] (X.X s) :=
        (X.adapted s).mono (𝓕.le_rightCont s) le_rfl
      have hDmeas : Measurable[𝓕.rightCont s] (D s) :=
        (hD.2.2.2 s).mono (𝓕.le_rightCont s) le_rfl
      have hRight : Measurable[𝓕.rightCont s] (fun ω => rightLimit D s ω) :=
        dividendStrategy_rightLimit_adapted_rightCont D hD s
      have hPost : Measurable[𝓕.rightCont s] (post s) := by
        exact ((measurable_const.add hXmeas).sub hDmeas).sub (hRight.sub hDmeas)
      have hPast : MeasurableSet[𝓕.rightCont s] {ω | ρ ω ≤ s} := by
        simpa only [WithTop.coe_le_coe] using hStop s
      exact Measurable.ite hPast measurable_const
        (measurable_const.mul (hDerClamp.measurable.comp hPost))
    · intro i _ ω
      dsimp only [weight]
      split_ifs with hρ
      · exact (norm_zero (E := ℝ)).trans_le (mul_nonneg (Real.exp_pos _).le hK)
      · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (hDiscount _ (by positivity) (by
          exact_mod_cast (lt_of_not_ge hρ).le.trans (hBound ω)))
          (hDerivativeBound _ (hClampIn _)) (norm_nonneg _) (Real.exp_pos _).le
  have hPaid : ∀ᵐ ω ∂P, IntegrableOn (paid ω) (Ioo (0 : ℝ) (ρ ω : ℝ)) (dividendMeasure D ω) := by
    filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hν] with ω hCont
    let A := Ioo (0 : ℝ) (ρ ω : ℝ)
    have hAM : MeasurableSet A := measurableSet_Ioo
    have hAfinite : dividendMeasure D ω A < ⊤ :=
      (measure_mono Ioo_subset_Ioc_self).trans_lt
        (dividendMeasure_Ioc_lt_top D hD ω 0 (ρ ω : ℝ))
    have hXtime : Measurable (fun s : ℝ => X.X s.toNNReal ω) :=
      hCont.measurable.comp ((show Monotone Real.toNNReal from fun _ _ h => Real.toNNReal_mono h).measurable)
    have hDtime : Measurable (fun s : ℝ => D s.toNNReal ω) :=
      ((hD.2.1 ω).comp (fun _ _ h => Real.toNNReal_mono h)).measurable
    have hRtime : Measurable (fun s : ℝ => rightLimit D s.toNNReal ω) :=
      ((avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω).comp
        (fun _ _ h => Real.toNNReal_mono h)).measurable
    have hPre : Measurable (fun s : ℝ => pre s.toNNReal ω) :=
      (measurable_const.add hXtime).sub hDtime
    have hJump : Measurable (fun s : ℝ => jump s.toNNReal ω) := hRtime.sub hDtime
    have hPost : Measurable (fun s : ℝ => post s.toNNReal ω) := hPre.sub hJump
    let calcPaid : ℝ → ℝ := fun s => Real.exp (-(q * s)) *
      (if jump s.toNNReal ω = 0 then deriv v (clamp (pre s.toNNReal ω))
        else (v (clamp (pre s.toNNReal ω)) - v (clamp (post s.toNNReal ω))) / jump s.toNNReal ω)
    have hCalcM : Measurable calcPaid := by
      apply ((measurable_const.mul measurable_id).neg.exp).mul
      apply Measurable.ite (hJump (measurableSet_singleton (0 : ℝ))) (hDerClamp.measurable.comp hPre)
      exact ((hVClamp.measurable.comp hPre).sub (hVClamp.measurable.comp hPost)).div hJump
    have hBands (s : ℝ) (hs : s ∈ A) :
        pre s.toNNReal ω ∈ Icc l u ∧ post s.toNNReal ω ∈ Icc l u := by
      apply hActive ω s.toNNReal (Real.toNNReal_pos.mpr hs.1)
      have hh : (s.toNNReal : ℝ) < (ρ ω : ℝ) := by
        simpa only [Real.coe_toNNReal s hs.1.le] using hs.2
      exact_mod_cast hh
    have hPaidMeas : AEStronglyMeasurable (paid ω) ((dividendMeasure D ω).restrict A) := by
      apply hCalcM.aestronglyMeasurable.congr
      filter_upwards [ae_restrict_mem hAM] with s hs
      simp only [calcPaid, paid, toll, hClampEq _ (hBands s hs).1, hClampEq _ (hBands s hs).2]
    apply IntegrableOn.of_bound hAfinite hPaidMeas (Real.exp (|q| * (T : ℝ)) * K)
    filter_upwards [ae_restrict_mem hAM] with s hs
    have hToll : ‖toll ω s‖ ≤ K := by
      have hJ : 0 ≤ jump s.toNNReal ω :=
        sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω s.toNNReal)
      rcases hBands s hs with ⟨hp, hpost⟩
      dsimp only [toll]
      split_ifs with hzero
      · exact hDerivativeBound _ hp
      · have hpos : 0 < jump s.toNNReal ω := lt_of_le_of_ne hJ (Ne.symm hzero)
        have hpz : post s.toNNReal ω < pre s.toNNReal ω := sub_lt_self _ hpos
        have hIncludes : Icc (post s.toNNReal ω) (pre s.toNNReal ω) ⊆ Icc l u :=
          fun y hy => ⟨hpost.1.trans hy.1, hy.2.trans hp.2⟩
        obtain ⟨y, hy, hSlope⟩ := exists_deriv_eq_slope v hpz
          (hv.continuousOn.mono (hIncludes.trans hInterval))
          ((hv.differentiableOn (by norm_num)).mono
            (Ioo_subset_Icc_self.trans (hIncludes.trans hInterval)))
        have hDiff : pre s.toNNReal ω - post s.toNNReal ω = jump s.toNNReal ω := by
          simp [post]
        rw [hDiff] at hSlope
        rw [← hSlope]
        exact hDerivativeBound _ (hIncludes (Ioo_subset_Icc_self hy))
    change ‖Real.exp (-(q * s)) * toll ω s‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hDiscount s hs.1.le (hs.2.le.trans (by exact_mod_cast hBound ω)))
      hToll (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨hRmeas, hConv⟩ := gaussian_positive_stieltjes_left_grid_L1_consistency
    X hX hBV hν q v a b l u hal hub hv x D hD ρ T hStop hBound hInitial hActive hTerminal
  have hL1 : Tendsto (fun j => ∫⁻ ω, ‖S j ω - residual ω‖ₑ ∂P) atTop (𝓝 0) := hConv
  have hRmeas' : AEStronglyMeasurable residual P := hRmeas
  have hMean : (∫ ω, residual ω ∂P) = 0 :=
    avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean P S residual
      hRmeas' (fun j => (hS j).1) (fun j => (hS j).2) hL1
  have hClose : ∀ᶠ j : ℕ in atTop, (∫⁻ ω, ‖S j ω - residual ω‖ₑ ∂P) < 1 :=
    hL1.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  obtain ⟨j, hj⟩ := hClose.exists
  have hDiffI : Integrable (fun ω => S j ω - residual ω) P :=
    ⟨(hS j).1.aestronglyMeasurable.sub hRmeas', hj.trans (by norm_num)⟩
  have hRI : Integrable residual P := by
    have hEq : (S j - fun ω => S j ω - residual ω) = residual := by
      funext ω
      exact sub_sub_cancel _ _
    simpa only [hEq] using (hS j).1.sub hDiffI
  refine ⟨residual, hRI, hMean, ?_⟩
  filter_upwards [hPaid] with ω hω
  refine ⟨hω, ?_⟩
  change Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) +
      (∫ s in Ioo (0 : ℝ) (ρ ω : ℝ), paid ω s ∂(dividendMeasure D ω)) =
    v (post 0 ω) + residual ω + (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s)
  dsimp only [residual]
  ring
