-- Prove2me | solution 1 for FeinbergPOMDP.WStar.obsLaw_weaklyContinuous
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:25:56.845273+00:00
-- url     : https://prove2.me/submissions/ac38243b-33ac-4519-bacf-21d39e7d03a8

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_ii

open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

/-- Two one-sided Fatou bounds give convergence of a bounded real sequence. -/
lemma fpw35_tendsto_of_fatou (b : ℕ → ℝ) (L M : ℝ) (hb : ∀ k, |b k| ≤ M) (hL : |L| ≤ M)
    (hplus : ENNReal.ofReal (M + L) ≤ liminf (fun k => ENNReal.ofReal (M + b k)) atTop)
    (hminus : ENNReal.ofReal (M - L) ≤ liminf (fun k => ENNReal.ofReal (M - b k)) atTop) :
    Tendsto b atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have lo : ∀ᶠ k in atTop, L - ε < b k := by
    by_cases h0 : M + L - ε < 0
    · exact Eventually.of_forall fun k => by
        have := (abs_le.1 (hb k)).1; linarith
    · push Not at h0
      have hlt : ENNReal.ofReal (M + L - ε) < ENNReal.ofReal (M + L) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      filter_upwards [eventually_lt_of_lt_liminf (hlt.trans_le hplus)] with k hk
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).1 hk
      linarith
  have hi : ∀ᶠ k in atTop, b k < L + ε := by
    by_cases h0 : M - L - ε < 0
    · exact Eventually.of_forall fun k => by
        have := (abs_le.1 (hb k)).2; linarith
    · push Not at h0
      have hlt : ENNReal.ofReal (M - L - ε) < ENNReal.ofReal (M - L) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      filter_upwards [eventually_lt_of_lt_liminf (hlt.trans_le hminus)] with k hk
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).1 hk
      linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (lo.and hi)
  exact ⟨N, fun k hk => by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [(hN k hk).1, (hN k hk).2]⟩

/-- `∫⁻ ofReal (M + f) = ofReal (M + ∫ f)` for bounded measurable `f` and a probability measure. -/
lemma fpw35_lintegral_shift {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (f : Y → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ y, |f y| ≤ M) :
    ∫⁻ y, ENNReal.ofReal (M + f y) ∂μ = ENNReal.ofReal (M + ∫ y, f y ∂μ) := by
  have hint : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable M
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
  have hi2 : Integrable (fun y => M + f y) μ := (integrable_const M).add hint
  rw [← ofReal_integral_eq_lintegral_ofReal hi2
    (Eventually.of_forall fun y => by
      have := (abs_le.1 (hM y)).1; simp only [Pi.zero_apply]; linarith)]
  rw [integral_add (integrable_const M) hint]
  simp

lemma fpw35_abs_integral_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (f : Y → ℝ) (M : ℝ) (hM : ∀ y, |f y| ≤ M) :
    |∫ y, f y ∂μ| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := M)
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
  simpa using this

/-- Dominated convergence for weakly converging probability measures and continuously
converging integrands (from Lemma 5.1(ii)). -/
lemma fpw35_weak_dct {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure Y) (μs : ℕ → ProbabilityMeasure Y) (hμ : Tendsto μs atTop (𝓝 μ))
    (f : ℕ → Y → ℝ) (g : Y → ℝ) (hf : ∀ k, Measurable (f k)) (hg : Measurable g) (M : ℝ)
    (hfM : ∀ k y, |f k y| ≤ M) (hgM : ∀ y, |g y| ≤ M)
    (hcc : ∀ y, Tendsto (fun p : ℕ × Y => f p.1 p.2) (atTop ×ˢ 𝓝 y) (𝓝 (g y))) :
    Tendsto (fun k => ∫ y, f k y ∂(μs k : Measure Y)) atTop (𝓝 (∫ y, g y ∂(μ : Measure Y))) := by
  let _ : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  have hfM' : ∀ k y, |-f k y| ≤ M := fun k y => by rw [abs_neg]; exact hfM k y
  have hgM' : ∀ y, |-g y| ≤ M := fun y => by rw [abs_neg]; exact hgM y
  refine fpw35_tendsto_of_fatou _ _ M (fun k => fpw35_abs_integral_le _ _ M (hfM k))
    (fpw35_abs_integral_le _ _ M hgM) ?_ ?_
  · have F := SchalAvg.AvgOpt.lemma_2_3_ii μ μs hμ (fun k y => ENNReal.ofReal (M + f k y))
      (fun k => ENNReal.measurable_ofReal.comp (measurable_const.add (hf k)))
    calc ENNReal.ofReal (M + ∫ y, g y ∂(μ : Measure Y))
        = ∫⁻ y, ENNReal.ofReal (M + g y) ∂(μ : Measure Y) :=
          (fpw35_lintegral_shift _ g hg M hgM).symm
      _ = ∫⁻ y, liminf (fun p : ℕ × Y => ENNReal.ofReal (M + f p.1 p.2)) (atTop ×ˢ 𝓝 y)
            ∂(μ : Measure Y) := by
          congr 1; funext y
          exact (((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_const_nhds.add (hcc y))).liminf_eq).symm
      _ ≤ _ := F
      _ = _ := by
          congr 1; funext k; exact fpw35_lintegral_shift _ (f k) (hf k) M (hfM k)
  · have F := SchalAvg.AvgOpt.lemma_2_3_ii μ μs hμ (fun k y => ENNReal.ofReal (M + -f k y))
      (fun k => ENNReal.measurable_ofReal.comp (measurable_const.add (hf k).neg))
    calc ENNReal.ofReal (M - ∫ y, g y ∂(μ : Measure Y))
        = ∫⁻ y, ENNReal.ofReal (M + -g y) ∂(μ : Measure Y) := by
          rw [fpw35_lintegral_shift _ (fun y => -g y) hg.neg M hgM', integral_neg, sub_eq_add_neg]
      _ = ∫⁻ y, liminf (fun p : ℕ × Y => ENNReal.ofReal (M + -f p.1 p.2)) (atTop ×ˢ 𝓝 y)
            ∂(μ : Measure Y) := by
          congr 1; funext y
          exact (((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_const_nhds.add (hcc y).neg)).liminf_eq).symm
      _ ≤ _ := F
      _ = _ := by
          congr 1; funext k
          rw [fpw35_lintegral_shift _ (fun y => -f k y) (hf k).neg M (hfM' k), integral_neg,
            sub_eq_add_neg]


lemma fpw_bind_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ] (f : β → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ y, |f y| ≤ M) :
    ∫ y, f y ∂(κ ∘ₘ μ) = ∫ x, ∫ y, f y ∂(κ x) ∂μ := by
  rw [← Measure.snd_compProd, Measure.snd,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    Measure.integral_compProd]
  exact Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable M
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hM p.2)

theorem solution {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsWeaklyContinuous (kernelPM Q)) :
    IsWeaklyContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) := by
  intro s ss hss
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  set M := ‖φ‖ with hMdef
  have hφb : ∀ y, |φ y| ≤ M := fun y => by simpa [Real.norm_eq_abs] using φ.norm_coe_le_norm y
  -- u(a, x') = ∫ φ dQ(·|a, x') is continuous and bounded
  let u : A × X → ℝ := fun q => ∫ y, φ y ∂(Q q)
  have hub : ∀ q, |u q| ≤ M := fun q => fpw35_abs_integral_le _ _ M hφb
  have huc : Continuous u := by
    refine continuous_iff_seqContinuous.2 fun {qs q} hqs => ?_
    have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (hQ q qs hqs)) φ
    exact this
  -- v(x, a) = ∫ u(a, x') P(dx'|x, a) is continuous and bounded
  let v : X × A → ℝ := fun p => ∫ x', u (p.2, x') ∂(P p)
  have hvb : ∀ p, |v p| ≤ M := fun p => fpw35_abs_integral_le _ _ M (fun x' => hub _)
  have hvc : Continuous v := by
    refine continuous_iff_seqContinuous.2 fun {ps p} hps => ?_
    have hpa : Tendsto (fun k => (ps k).2) atTop (𝓝 p.2) := (continuous_snd.tendsto _).comp hps
    refine fpw35_weak_dct (kernelPM P p) (fun k => kernelPM P (ps k)) (hP p ps hps)
      (fun k x' => u ((ps k).2, x')) (fun x' => u (p.2, x'))
      (fun k => (huc.comp (continuous_const.prodMk continuous_id)).measurable)
      (huc.comp (continuous_const.prodMk continuous_id)).measurable M
      (fun k x' => hub _) (fun x' => hub _) ?_
    intro x'
    have ht : Tendsto (fun q : ℕ × X => ((ps q.1).2, q.2)) (atTop ×ˢ 𝓝 x') (𝓝 (p.2, x')) :=
      (hpa.comp tendsto_fst).prodMk_nhds tendsto_snd
    exact (huc.tendsto _).comp ht
  -- identity: ∫ φ dR′(z, a) = ∫ v(x, a) z(dx)
  have hid : ∀ (z : ProbabilityMeasure X) (a : A),
      ∫ y, φ y ∂(obsLaw P Q z a : Measure Y) = ∫ x, v (x, a) ∂(z : Measure X) := by
    intro z a
    have hum : Measurable fun x' : X => u (a, x') :=
      (huc.comp (continuous_const.prodMk continuous_id)).measurable
    rw [obsLaw, ProbabilityMeasure.toMeasure_map]
    change ∫ y, φ y ∂((((P.comap (fun x => (x, a)) measurable_prodMk_right) ∘ₘ (z : Measure X)) ⊗ₘ
      (Q.comap (fun x' => (a, x')) measurable_prodMk_left)).snd) = _
    rw [Measure.snd_compProd,
      fpw_bind_integral _ _ φ φ.continuous.measurable M hφb]
    exact fpw_bind_integral _ _ (fun x' => u (a, x')) hum M (fun x' => hub _)
  simp only [hid]
  refine fpw35_weak_dct s.1 (fun k => (ss k).1) ((continuous_fst.tendsto _).comp hss)
    (fun k x => v (x, (ss k).2)) (fun x => v (x, s.2))
    (fun k => (hvc.comp (continuous_id.prodMk continuous_const)).measurable)
    (hvc.comp (continuous_id.prodMk continuous_const)).measurable M
    (fun k x => hvb _) (fun x => hvb _) ?_
  intro x
  have ht : Tendsto (fun q : ℕ × X => (q.2, (ss q.1).2)) (atTop ×ˢ 𝓝 x) (𝓝 (x, s.2)) :=
    tendsto_snd.prodMk_nhds (((continuous_snd.tendsto _).comp hss).comp tendsto_fst)
  exact (hvc.tendsto _).comp ht
