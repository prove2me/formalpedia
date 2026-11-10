-- Prove2me | solution 1 for GameRandEnv.FirstOrder.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T20:00:14.05599+00:00
-- url     : https://prove2.me/submissions/7bd26288-aa61-47d7-ac7d-c80c81f92b69

import Mathlib
import Definitions.Def_GameRandEnv_FirstOrder_Setting

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GameRandEnv.FirstOrder.Aux

open GameRandEnv.FirstOrder

variable {d : ℕ} {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]

lemma mix_zero (ν ν' : Measure (Rd d × Y)) : mix 0 ν ν' = ν := by
  simp [mix]

lemma mix_one (ν ν' : Measure (Rd d × Y)) : mix 1 ν ν' = ν' := by
  simp [mix]

/-- finite `p`-th moment does not depend on the base point -/
lemma moment_lt_top_of_base {p : ℝ} (hp : 1 ≤ p) {π : Measure (Rd d × Y)} [IsFiniteMeasure π]
    (z0 z1 : Rd d × Y) (h : ∫⁻ z, ENNReal.ofReal (dist z z0 ^ p) ∂π < ∞) :
    ∫⁻ z, ENNReal.ofReal (dist z z1 ^ p) ∂π < ∞ := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have key : ∀ z, ENNReal.ofReal (dist z z1 ^ p) ≤
      2 ^ (p - 1) * (ENNReal.ofReal (dist z z0 ^ p) + ENNReal.ofReal (dist z0 z1 ^ p)) := by
    intro z
    rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0, ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0,
      ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0, ← edist_dist, ← edist_dist, ← edist_dist]
    calc edist z z1 ^ p ≤ (edist z z0 + edist z0 z1) ^ p :=
          ENNReal.rpow_le_rpow (edist_triangle _ _ _) hp0
      _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
  have h2 : (2 : ℝ≥0∞) ^ (p - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  calc ∫⁻ z, ENNReal.ofReal (dist z z1 ^ p) ∂π
      ≤ ∫⁻ z, 2 ^ (p - 1) * (ENNReal.ofReal (dist z z0 ^ p) + ENNReal.ofReal (dist z0 z1 ^ p)) ∂π :=
        lintegral_mono key
    _ = 2 ^ (p - 1) * (∫⁻ z, ENNReal.ofReal (dist z z0 ^ p) ∂π
          + ENNReal.ofReal (dist z0 z1 ^ p) * π Set.univ) := by
        rw [lintegral_const_mul' _ _ h2, lintegral_add_right _ measurable_const, lintegral_const]
    _ < ∞ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 h2)
          (ENNReal.add_lt_top.2 ⟨h, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩)

lemma mix_mem_Pi {m : Measure Y} {p : ℝ} (hp : 1 ≤ p) {ν ν' : Measure (Rd d × Y)}
    (hν : ν ∈ Pi (d := d) m p) (hν' : ν' ∈ Pi (d := d) m p) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : mix t ν ν' ∈ Pi (d := d) m p := by
  obtain ⟨h1, h2, z0, h3⟩ := hν
  obtain ⟨h1', h2', z0', h3'⟩ := hν'
  have hsum : ENNReal.ofReal (1 - t) + ENNReal.ofReal t = 1 := by
    rw [← ENNReal.ofReal_add (by linarith [ht.2]) ht.1]; simp
  refine ⟨⟨?_⟩, ?_, z0, ?_⟩
  · simp only [mix, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact hsum
  · simp only [mix]
    rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, h2, h2',
      ← add_smul, hsum, one_smul]
  · have h3'' := moment_lt_top_of_base hp z0' z0 h3'
    simp only [mix]
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top h3,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top h3''⟩


/-! ## L1: integrability from growth, integrals over mixtures -/

section L1
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma ofReal_dist_rpow_le {p : ℝ} (hp : 1 ≤ p) (a b c : Rd d × Y) :
    ENNReal.ofReal (dist a c ^ p) ≤
      2 ^ (p - 1) * (ENNReal.ofReal (dist a b ^ p) + ENNReal.ofReal (dist b c ^ p)) := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0, ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0,
    ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0, ← edist_dist, ← edist_dist, ← edist_dist]
  calc edist a c ^ p ≤ (edist a b + edist b c) ^ p :=
        ENNReal.rpow_le_rpow (edist_triangle _ _ _) hp0
    _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp

lemma measurable_dist_rpow (p : ℝ) (z1 : Rd d × Y) :
    Measurable (fun z : Rd d × Y => dist z z1 ^ p) :=
  ((continuous_id.dist continuous_const).measurable).pow_const p

lemma integrable_dist_rpow {m : Measure Y} {p : ℝ} (hp : 1 ≤ p) {π : Measure (Rd d × Y)}
    (hπ : π ∈ Pi (d := d) m p) (z1 : Rd d × Y) :
    Integrable (fun z => dist z z1 ^ p) π := by
  obtain ⟨h1, -, z0, h3⟩ := hπ
  have h := moment_lt_top_of_base hp z0 z1 h3
  have := integrable_toReal_of_lintegral_ne_top
    ((measurable_dist_rpow p z1).ennreal_ofReal.aemeasurable) h.ne
  refine this.congr (ae_of_all _ fun z => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg dist_nonneg _)]

lemma integrable_of_growth {m : Measure Y} {p : ℝ} (hp : 1 ≤ p) {π : Measure (Rd d × Y)}
    (hπ : π ∈ Pi (d := d) m p) {g : Rd d × Y → ℝ} (hg : Measurable g) (C : ℝ) (z1 : Rd d × Y)
    (hb : ∀ z, |g z| ≤ C * (1 + dist z z1 ^ p)) : Integrable g π := by
  haveI := hπ.1
  have hint : Integrable (fun z => C * (1 + dist z z1 ^ p)) π :=
    ((integrable_const 1).add (integrable_dist_rpow hp hπ z1)).const_mul C
  exact hint.mono' hg.aestronglyMeasurable
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hb z)

end L1

lemma integral_mix {ν ν' : Measure (Rd d × Y)} {g : Rd d × Y → ℝ} (hg : Integrable g ν)
    (hg' : Integrable g ν') {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ z, g z ∂(mix t ν ν') = (1 - t) * ∫ z, g z ∂ν + t * ∫ z, g z ∂ν' := by
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
  simp only [mix]
  rw [integral_add_measure (hg.smul_measure ENNReal.ofReal_ne_top)
      (hg'.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal h1t, ENNReal.toReal_ofReal ht.1, smul_eq_mul, smul_eq_mul]

lemma pairDiff_mix {ν ν' : Measure (Rd d × Y)} {g : Rd d × Y → ℝ} (hg : Integrable g ν)
    (hg' : Integrable g ν') {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    pairDiff g ν (mix s ν ν') = s * pairDiff g ν ν' := by
  simp only [pairDiff]
  rw [integral_mix hg hg' hs]; ring

lemma mix_mix (ν ν' : Measure (Rd d × Y)) {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : mix t ν (mix s ν ν') = mix (t * s) ν ν' := by
  have h1 : ENNReal.ofReal (1 - t) + ENNReal.ofReal t * ENNReal.ofReal (1 - s)
      = ENNReal.ofReal (1 - t * s) := by
    rw [← ENNReal.ofReal_mul ht.1, ← ENNReal.ofReal_add (by linarith [ht.2])
      (mul_nonneg ht.1 (by linarith [hs.2]))]
    congr 1; ring
  have h2 : ENNReal.ofReal t * ENNReal.ofReal s = ENNReal.ofReal (t * s) :=
    (ENNReal.ofReal_mul ht.1).symm
  simp only [mix]
  rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, h1, h2]

/-! ## L2: `W_p (ν, mix u ν ν') → 0` and continuity of `δF` along the segment -/

section L2
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma wasserstein_mix_le {p : ℝ} (hp : 1 ≤ p) (ν ν' : Measure (Rd d × Y))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    wasserstein p ν (mix u ν ν') ≤
      (ENNReal.ofReal u * ∫⁻ q, ENNReal.ofReal (dist q.1 q.2 ^ p) ∂(ν.prod ν')) ^ (1 / p) := by
  have hp0 : (0 : ℝ) < p := by linarith
  set γ : Measure ((Rd d × Y) × (Rd d × Y)) :=
    ENNReal.ofReal (1 - u) • ν.map (fun z => (z, z)) + ENNReal.ofReal u • ν.prod ν' with hγ
  have hdiag : Measurable (fun z : Rd d × Y => (z, z)) := measurable_id.prodMk measurable_id
  have hsum : ENNReal.ofReal (1 - u) + ENNReal.ofReal u = 1 := by
    rw [← ENNReal.ofReal_add (by linarith [hu.2]) hu.1]; simp
  have hfst : γ.map Prod.fst = ν := by
    rw [hγ, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
      Measure.map_map measurable_fst hdiag, Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
    rw [show (Prod.fst ∘ fun z : Rd d × Y => (z, z)) = id from rfl, Measure.map_id,
      ← add_smul, hsum, one_smul]
  have hsnd : γ.map Prod.snd = mix u ν ν' := by
    rw [hγ, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
      Measure.map_map measurable_snd hdiag, Measure.map_snd_prod]
    simp only [measure_univ, one_smul]
    rw [show (Prod.snd ∘ fun z : Rd d × Y => (z, z)) = id from rfl, Measure.map_id]
    rfl
  have hmeas : Measurable (fun q : (Rd d × Y) × (Rd d × Y) => ENNReal.ofReal (dist q.1 q.2 ^ p)) :=
    ((continuous_fst.dist continuous_snd).measurable.pow_const p).ennreal_ofReal
  have hcost : ∫⁻ q, ENNReal.ofReal (dist q.1 q.2 ^ p) ∂γ =
      ENNReal.ofReal u * ∫⁻ q, ENNReal.ofReal (dist q.1 q.2 ^ p) ∂(ν.prod ν') := by
    rw [hγ, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_map hmeas hdiag]
    simp [Real.zero_rpow hp0.ne']
  unfold wasserstein
  rw [← hcost]
  exact ENNReal.rpow_le_rpow (iInf₂_le γ ⟨hfst, hsnd⟩) (by positivity)

lemma lintegral_prod_dist_lt_top {m : Measure Y} {p : ℝ} (hp : 1 ≤ p) {ν ν' : Measure (Rd d × Y)}
    (hν : ν ∈ Pi (d := d) m p) (hν' : ν' ∈ Pi (d := d) m p) :
    ∫⁻ q, ENNReal.ofReal (dist q.1 q.2 ^ p) ∂(ν.prod ν') < ∞ := by
  haveI := hν.1; haveI := hν'.1
  obtain ⟨-, -, z0, h3⟩ := hν
  obtain ⟨-, -, z0', h3'⟩ := hν'
  have h3'' := moment_lt_top_of_base hp z0' z0 h3'
  have ha : Measurable (fun z : Rd d × Y => ENNReal.ofReal (dist z z0 ^ p)) :=
    (measurable_dist_rpow p z0).ennreal_ofReal
  have h2 : (2 : ℝ≥0∞) ^ (p - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  calc ∫⁻ q, ENNReal.ofReal (dist q.1 q.2 ^ p) ∂(ν.prod ν')
      ≤ ∫⁻ q, 2 ^ (p - 1) * (ENNReal.ofReal (dist q.1 z0 ^ p) + ENNReal.ofReal (dist q.2 z0 ^ p))
          ∂(ν.prod ν') := lintegral_mono fun q => by
        have := ofReal_dist_rpow_le hp q.1 z0 q.2
        rwa [dist_comm z0 q.2] at this
    _ = 2 ^ (p - 1) * (∫⁻ z, ENNReal.ofReal (dist z z0 ^ p) ∂ν
          + ∫⁻ z, ENNReal.ofReal (dist z z0 ^ p) ∂ν') := by
        rw [lintegral_const_mul' _ _ h2, lintegral_add_left (f := fun q : (Rd d × Y) × (Rd d × Y) =>
          ENNReal.ofReal (dist q.1 z0 ^ p)) (ha.comp measurable_fst)]
        congr 2
        · rw [← lintegral_map ha measurable_fst, Measure.map_fst_prod]; simp
        · rw [← lintegral_map ha measurable_snd, Measure.map_snd_prod]; simp
    _ < ∞ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 h2) (ENNReal.add_lt_top.2 ⟨h3, h3''⟩)

lemma tendsto_wasserstein_mix {m : Measure Y} {p : ℝ} (hp : 1 ≤ p) {ν ν' : Measure (Rd d × Y)}
    (hν : ν ∈ Pi (d := d) m p) (hν' : ν' ∈ Pi (d := d) m p) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u in 𝓝[Set.Icc (0 : ℝ) 1] 0, wasserstein p ν (mix u ν ν') < ENNReal.ofReal δ := by
  haveI := hν.1; haveI := hν'.1
  set K := ∫⁻ q, ENNReal.ofReal (dist q.1 q.2 ^ p) ∂(ν.prod ν')
  have hK : K ≠ ∞ := (lintegral_prod_dist_lt_top hp hν hν').ne
  have hp0 : (0 : ℝ) < 1 / p := by
    have : (0:ℝ) < p := by linarith
    positivity
  have hlim : Tendsto (fun u : ℝ => (ENNReal.ofReal u * K) ^ (1 / p)) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => ENNReal.ofReal u * K) (𝓝 0) (𝓝 (ENNReal.ofReal 0 * K)) :=
      ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto 0) (Or.inr hK)
    have h2 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto _).comp h1
    rw [ENNReal.ofReal_zero, zero_mul, ENNReal.zero_rpow_of_pos hp0] at h2
    exact h2
  have hev := (tendsto_order.1 (hlim.mono_left (nhdsWithin_le_nhds (s := Set.Icc (0 : ℝ) 1)))).2 _ (ENNReal.ofReal_pos.2 hδ)
  filter_upwards [hev, self_mem_nhdsWithin] with u hu hmem
  exact lt_of_le_of_lt (wasserstein_mix_le hp ν ν' hmem) hu

variable {m : Measure Y} {p : ℝ} {F : Measure (Rd d × Y) → ℝ} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ}

lemma tendsto_dF_mix (hA : Assumption21 m p F δF) {ν ν' : Measure (Rd d × Y)}
    (hν : ν ∈ Pi (d := d) m p) (hν' : ν' ∈ Pi (d := d) m p) (x : Rd d) (y : Y) :
    Tendsto (fun u => δF (mix u ν ν') x y) (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 (δF ν x y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := hA.contDeriv x y ν hν ε hε
  filter_upwards [tendsto_wasserstein_mix hA.one_le_p hν hν' hδ, self_mem_nhdsWithin] with u hu hmem
  rw [Real.dist_eq]
  exact hcont _ (mix_mem_Pi hA.one_le_p hν hν' hmem) hu

/-- `G u = ∫ δF(mix u ν ν') d(ν' - ν)` is continuous at `u = 0` (within `[0,1]`). -/
lemma tendsto_pairDiff_mix (hA : Assumption21 m p F δF) {ν ν' : Measure (Rd d × Y)}
    (hν : ν ∈ Pi (d := d) m p) (hν' : ν' ∈ Pi (d := d) m p) :
    Tendsto (fun u => pairDiff (fun z => δF (mix u ν ν') z.1 z.2) ν ν') (𝓝[Set.Icc (0 : ℝ) 1] 0)
      (𝓝 (pairDiff (fun z => δF ν z.1 z.2) ν ν')) := by
  obtain ⟨C, y₀, hC⟩ := hA.growth
  have hp := hA.one_le_p
  have key : ∀ μ ∈ Pi (d := d) m p, Tendsto (fun u => ∫ z, δF (mix u ν ν') z.1 z.2 ∂μ)
      (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 (∫ z, δF ν z.1 z.2 ∂μ)) := by
    intro μ hμ
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => C * (1 + dist z ((0 : Rd d), y₀) ^ p)) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hA.linDeriv.1 _ (mix_mem_Pi hp hν hν' hu)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact ae_of_all _ fun z => by
        simpa [Real.norm_eq_abs] using hC _ (mix_mem_Pi hp hν hν' hu) z.1 z.2
    · haveI := hμ.1
      exact ((integrable_const 1).add (integrable_dist_rpow hp hμ _)).const_mul C
    · exact ae_of_all _ fun z => tendsto_dF_mix hA hν hν' z.1 z.2
  exact (key ν' hν').sub (key ν hν)

/-! ## L3: directional derivative of `F` along mixtures -/

lemma tendsto_slope_F (hA : Assumption21 m p F δF) {ν ν' : Measure (Rd d × Y)}
    (hν : ν ∈ Pi (d := d) m p) (hν' : ν' ∈ Pi (d := d) m p) :
    Tendsto (fun s => (F (mix s ν ν') - F ν) / s) (𝓝[>] 0)
      (𝓝 (pairDiff (fun z => δF ν z.1 z.2) ν ν')) := by
  obtain ⟨C, y₀, hC⟩ := hA.growth
  have hp := hA.one_le_p
  set G : ℝ → ℝ := fun u => pairDiff (fun z => δF (mix u ν ν') z.1 z.2) ν ν' with hG
  have hint : ∀ π ∈ Pi (d := d) m p, ∀ μ ∈ Pi (d := d) m p,
      Integrable (fun z : Rd d × Y => δF π z.1 z.2) μ := fun π hπ μ hμ =>
    integrable_of_growth hp hμ (hA.linDeriv.1 π hπ) C _ fun z => hC π hπ z.1 z.2
  have hEq : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      pairDiff (fun z => δF (mix t ν (mix s ν ν')) z.1 z.2) ν (mix s ν ν') = s * G (t * s) := by
    intro s hs' t ht
    have hts : t * s ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg ht.1 hs'.1, by nlinarith [ht.1, ht.2, hs'.1, hs'.2]⟩
    simp only [hG]
    rw [mix_mix ν ν' ht hs', pairDiff_mix (hint _ (mix_mem_Pi hp hν hν' hts) ν hν)
      (hint _ (mix_mem_Pi hp hν hν' hts) ν' hν') hs']
  -- the quotient is an average of `G` over `[0, s]`
  have hq : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      (F (mix s ν ν') - F ν) / s = ∫ t in (0 : ℝ)..1, G (t * s) := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    obtain ⟨-, hF⟩ := hA.linDeriv.2 ν hν _ (mix_mem_Pi hp hν hν' hs')
    have heq : Set.EqOn (fun t => pairDiff (fun z => δF (mix t ν (mix s ν ν')) z.1 z.2) ν
        (mix s ν ν')) (fun t => s * G (t * s)) (Set.uIcc 0 1) := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact hEq s hs' t ht
    rw [hF, intervalIntegral.integral_congr heq, intervalIntegral.integral_const_mul]
    field_simp [hs.1.ne']
  have hIIG : ∀ s ∈ Set.Ioc (0 : ℝ) 1, IntervalIntegrable (fun t => G (t * s)) volume 0 1 := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    obtain ⟨hII, -⟩ := hA.linDeriv.2 ν hν _ (mix_mem_Pi hp hν hν' hs')
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hII ⊢
    have h2 : IntegrableOn (fun t => s⁻¹ * pairDiff (fun z => δF (mix t ν (mix s ν ν')) z.1 z.2) ν
        (mix s ν ν')) (Set.Ioc (0 : ℝ) 1) := Integrable.const_mul hII s⁻¹
    refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioc
    show s⁻¹ * _ = G (t * s)
    rw [hEq s hs' t ⟨ht.1.le, ht.2⟩]
    field_simp [hs.1.ne']
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hG0 := tendsto_pairDiff_mix hA hν hν'
  rw [Metric.tendsto_nhdsWithin_nhds] at hG0
  obtain ⟨δ, hδ, hδG⟩ := hG0 (ε / 2) (by linarith)
  refine ⟨min δ 1, lt_min hδ one_pos, fun {s} hs hsd => ?_⟩
  have hs0 : (0 : ℝ) < s := hs
  have hsd' : s < min δ 1 := by rwa [Real.dist_eq, sub_zero, abs_of_pos hs0] at hsd
  have hsI : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs0, (lt_of_lt_of_le hsd' (min_le_right _ _)).le⟩
  rw [hq s hsI, Real.dist_eq]
  have hG0' : G 0 = pairDiff (fun z => δF ν z.1 z.2) ν ν' := by simp [hG, mix_zero]
  rw [← hG0', show G 0 = ∫ _t in (0 : ℝ)..1, G 0 by simp,
    ← intervalIntegral.integral_sub (hIIG s hsI) intervalIntegrable_const]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖G (t * s) - G 0‖ ≤ ε / 2 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hts : t * s ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg ht.1.le hs0.le, by nlinarith [ht.1, ht.2, hsI.2]⟩
    have hd : dist (t * s) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hts.1]
      calc t * s ≤ 1 * s := by nlinarith [ht.2]
        _ < δ := by linarith [lt_of_lt_of_le hsd' (min_le_left _ _)]
    have := hδG hts hd
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs, hG0']; exact this.le
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs] at this
  calc _ ≤ ε / 2 * |(1 : ℝ) - 0| := this
    _ < ε := by norm_num; linarith

/-- Convexity along mixtures turns the directional derivative into a supporting line. -/
lemma pairDiff_le_of_convex (hA : Assumption21 m p F δF) (hconv : ConvexOnPi (d := d) m p F)
    {ν ν' : Measure (Rd d × Y)} (hν : ν ∈ Pi (d := d) m p) (hν' : ν' ∈ Pi (d := d) m p) :
    pairDiff (fun z => δF ν z.1 z.2) ν ν' ≤ F ν' - F ν := by
  refine le_of_tendsto (tendsto_slope_F hA hν hν') ?_
  have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
  filter_upwards [this] with s hs
  rw [div_le_iff₀ hs.1]
  have := hconv ν hν ν' hν' s ⟨hs.1.le, hs.2.le⟩
  linarith

end L2


/-! ## L4: the constant `c(y)` of the first-order condition and its bounds -/

section L4

/-- On a good slice, the potential `δF + η log ρ` is constant in `x` (zero gradient, `ℝ^d` connected). -/
lemma foc_const_slice {π : Measure (Rd d × Y)} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ} {η : ℝ}
    {ρ : Rd d × Y → ℝ} {y : Y}
    (hdF : ContDiff ℝ 1 (fun x => δF π x y))
    (hy : ∀ x : Rd d, 0 < ρ (x, y) ∧ DifferentiableAt ℝ (fun x' => Real.log (ρ (x', y))) x ∧
      gradient (fun x' => δF π x' y) x + η • gradient (fun x' => Real.log (ρ (x', y))) x = 0) :
    ∀ x, δF π x y + η * Real.log (ρ (x, y)) = δF π 0 y + η * Real.log (ρ (0, y)) := by
  have hd1 : Differentiable ℝ (fun x => δF π x y) := hdF.differentiable one_ne_zero
  have hφ : Differentiable ℝ (fun x => δF π x y + η * Real.log (ρ (x, y))) := fun x =>
    (hd1 x).add ((hy x).2.1.const_mul η)
  have hf : ∀ x, fderiv ℝ (fun x => δF π x y + η * Real.log (ρ (x, y))) x = 0 := by
    intro x
    have h := (hy x).2.2
    have hg : gradient (fun x => δF π x y + η * Real.log (ρ (x, y))) x = 0 := by
      unfold gradient at h ⊢
      rw [fderiv_fun_add (hd1 x) ((hy x).2.1.const_mul η), fderiv_const_mul (hy x).2.1 η, map_add,
        map_smul]
      exact h
    unfold gradient at hg
    simpa using hg
  intro x
  exact is_const_of_fderiv_eq_zero hφ hf x 0

/-- The `x`-slices of the density of a measure with `Y`-marginal `m` integrate to one. -/
lemma slice_lintegral_eq_one {m : Measure Y} [IsProbabilityMeasure m] {π : Measure (Rd d × Y)}
    {ρ : Rd d × Y → ℝ} (hρ : Measurable ρ)
    (hπ : π = (volume.prod m).withDensity (fun z => ENNReal.ofReal (ρ z)))
    (hm : π.map Prod.snd = m) :
    ∀ᵐ y ∂m, ∫⁻ x, ENNReal.ofReal (ρ (x, y)) = 1 := by
  have hf : Measurable (fun y => ∫⁻ x, ENNReal.ofReal (ρ (x, y))) :=
    (hρ.ennreal_ofReal).lintegral_prod_left'
  have key : m.withDensity (fun y => ∫⁻ x, ENNReal.ofReal (ρ (x, y))) = m.withDensity 1 := by
    rw [withDensity_one]
    ext A hA
    rw [withDensity_apply _ hA]
    conv_rhs => rw [← hm]
    rw [Measure.map_apply measurable_snd hA, hπ, withDensity_apply _ (measurable_snd hA),
      ← Set.univ_prod, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod_symm _ hρ.ennreal_ofReal.aemeasurable]
  have := (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable aemeasurable_const).1 key
  filter_upwards [this] with y hy
  simpa using hy

lemma dist_rpow_le_of_norm_le_one {p : ℝ} (hp : 0 ≤ p) {x : Rd d} (hx : ‖x‖ ≤ 1) (y y₀ : Y) :
    dist (x, y) ((0 : Rd d), y₀) ^ p ≤ 1 + dist y y₀ ^ p := by
  rw [Prod.dist_eq, dist_zero_right]
  rcases le_total ‖x‖ (dist y y₀) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]
    have h1 : ‖x‖ ^ p ≤ 1 := Real.rpow_le_one (norm_nonneg _) hx hp
    have h2 : 0 ≤ dist y y₀ ^ p := Real.rpow_nonneg dist_nonneg _
    linarith

/-- Upper bound for the constant on one slice: the slice density integrates to at most one. -/
lemma c_upper_slice {η : ℝ} (hη : 0 < η) {g ρ : Rd d → ℝ} {c A : ℝ}
    (hpos : ∀ x, 0 < ρ x) (hc : ∀ x, g x + η * Real.log (ρ x) = c)
    (hA : ∀ x, ‖x‖ ≤ 1 → g x ≤ A) (h1 : ∫⁻ x, ENNReal.ofReal (ρ x) ≤ 1) :
    c ≤ A + η * Real.log ((volume (Metric.closedBall (0 : Rd d) 1)).toReal)⁻¹ := by
  set B := Metric.closedBall (0 : Rd d) 1
  have hB0 : 0 < volume B := Metric.measure_closedBall_pos _ _ one_pos
  have hBt : volume B < ∞ := measure_closedBall_lt_top
  set E := Real.exp ((c - A) / η)
  have hρE : ∀ x ∈ B, ENNReal.ofReal E ≤ ENNReal.ofReal (ρ x) := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    have hx' : ‖x‖ ≤ 1 := by simpa [B] using hx
    have hρ : ρ x = Real.exp ((c - g x) / η) := by
      rw [← Real.exp_log (hpos x)]; congr 1
      have := hc x; field_simp; linarith
    rw [hρ]
    apply Real.exp_le_exp.2
    have := hA x hx'
    exact div_le_div_of_nonneg_right (by linarith) hη.le
  have hle : ENNReal.ofReal E * volume B ≤ 1 := by
    calc ENNReal.ofReal E * volume B = ∫⁻ x in B, ENNReal.ofReal E := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in B, ENNReal.ofReal (ρ x) := setLIntegral_mono' measurableSet_closedBall hρE
      _ ≤ ∫⁻ x, ENNReal.ofReal (ρ x) := setLIntegral_le_lintegral _ _
      _ ≤ 1 := h1
  have hvB : 0 < (volume B).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
  have hreal : E * (volume B).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_one] at this
  have hE : E ≤ ((volume B).toReal)⁻¹ := by
    calc E = E * (volume B).toReal * ((volume B).toReal)⁻¹ := by field_simp
      _ ≤ 1 * ((volume B).toReal)⁻¹ := mul_le_mul_of_nonneg_right hreal (inv_nonneg.2 hvB.le)
      _ = _ := one_mul _
  have hlog : (c - A) / η ≤ Real.log ((volume B).toReal)⁻¹ := by
    rw [← Real.log_exp ((c - A) / η)]
    exact Real.log_le_log (Real.exp_pos _) hE
  rw [div_le_iff₀ hη] at hlog
  linarith

/-- Pointwise entropy tail bound: `t (log t)⁻ ≤ t (-log g) + 2 √g` for `0 < g ≤ 1`. -/
lemma neg_log_mul_le {t g : ℝ} (ht : 0 < t) (hg0 : 0 < g) (hg1 : g ≤ 1) :
    t * max (-Real.log t) 0 ≤ t * (-Real.log g) + 2 * Real.sqrt g := by
  have hlg : 0 ≤ -Real.log g := by have := Real.log_nonpos hg0.le hg1; linarith
  have hsg : 0 ≤ Real.sqrt g := Real.sqrt_nonneg _
  rcases le_total g t with h | h
  · have : max (-Real.log t) 0 ≤ -Real.log g := by
      apply max_le _ hlg
      have := Real.log_le_log hg0 h; linarith
    nlinarith
  · have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hlog : -Real.log t = 2 * Real.log (Real.sqrt t)⁻¹ := by
      rw [Real.log_inv, Real.log_sqrt ht.le]; ring
    have h2 : Real.log (Real.sqrt t)⁻¹ ≤ (Real.sqrt t)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.2 hst)
    have htt : t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt ht.le).symm
    have hm : max (-Real.log t) 0 ≤ 2 * (Real.sqrt t)⁻¹ := by
      apply max_le
      · rw [hlog]; linarith
      · positivity
    have h3 : t * max (-Real.log t) 0 ≤ 2 * Real.sqrt t := by
      calc t * max (-Real.log t) 0 ≤ t * (2 * (Real.sqrt t)⁻¹) :=
            mul_le_mul_of_nonneg_left hm ht.le
        _ = 2 * (t / Real.sqrt t) := by ring
        _ = 2 * Real.sqrt t := by rw [Real.div_sqrt]
    have h4 : Real.sqrt t ≤ Real.sqrt g := Real.sqrt_le_sqrt h
    nlinarith

end L4

/-! ## L4b: integrability of `log ρ` for a first-order-condition density -/

section L4b
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma le_one_add_rpow {a p : ℝ} (ha : 0 ≤ a) (hp : 1 ≤ p) : a ≤ 1 + a ^ p := by
  rcases le_total a 1 with h | h
  · have := Real.rpow_nonneg ha p; linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hp
    rw [Real.rpow_one] at this; linarith

/-- `log ρ` is `π`-integrable when it has a growth upper bound (the negative part is controlled by
the entropy tail bound against the integrable weight `(1+‖x‖)^{-(2d+2)}`). -/
lemma integrable_log_dens {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ} (hp : 1 ≤ p)
    {π : Measure (Rd d × Y)} (hπP : π ∈ Pi (d := d) m p) {ρ : Rd d × Y → ℝ} (hρ : Measurable ρ)
    (hπ : π = (volume.prod m).withDensity (fun z => ENNReal.ofReal (ρ z)))
    {K : ℝ} (z1 : Rd d × Y)
    (hup : ∀ᵐ z ∂π, Real.log (ρ z) ≤ K * (1 + dist z z1 ^ p)) :
    Integrable (fun z => Real.log (ρ z)) π := by
  haveI := hπP.1
  have hlogm : Measurable (fun z => Real.log (ρ z)) := Real.measurable_log.comp hρ
  set r : ℝ := 2 * (d : ℝ) + 2 with hr
  have hr0 : 0 < r := by positivity
  set g : Rd d → ℝ := fun x => (1 + ‖x‖) ^ (-r) with hg
  have hg0 : ∀ x, 0 < g x := fun x => Real.rpow_pos_of_pos (by positivity) _
  have hg1 : ∀ x, g x ≤ 1 := fun x =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith)
  have hlg : ∀ x, -Real.log (g x) ≤ r * ‖x‖ := by
    intro x
    rw [hg, Real.log_rpow (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖x‖ by positivity)
    nlinarith
  have hsq : ∀ x, Real.sqrt (g x) = (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
    intro x
    rw [Real.sqrt_eq_rpow, hg, ← Real.rpow_mul (by positivity)]
    congr 1; rw [hr]; ring
  have hsqi : Integrable (fun x : Rd d => 2 * Real.sqrt (g x)) volume := by
    have h := integrable_one_add_norm (E := Rd d) (μ := volume) (r := (d : ℝ) + 1)
      (by rw [finrank_euclideanSpace_fin]; linarith)
    simpa only [hsq] using h.const_mul 2
  -- integrability of `‖x‖`
  have hnorm : Integrable (fun z : Rd d × Y => r * ‖z.1‖) π := by
    refine integrable_of_growth hp hπP (by fun_prop) r ((0 : Rd d), z1.2) fun z => ?_
    have h1 : ‖z.1‖ ≤ dist z ((0 : Rd d), z1.2) := by
      rw [Prod.dist_eq, ← dist_zero_right]; exact le_max_left _ _
    have h2 := le_one_add_rpow (dist_nonneg (x := z) (y := ((0 : Rd d), z1.2))) hp
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) hr0.le
  -- the negative part has finite integral
  have hneg : ∫⁻ z, ENNReal.ofReal (max (-Real.log (ρ z)) 0) ∂π < ∞ := by
    have hmeas : Measurable (fun z => ENNReal.ofReal (max (-Real.log (ρ z)) 0)) :=
      (hlogm.neg.max measurable_const).ennreal_ofReal
    rw [hπ, lintegral_withDensity_eq_lintegral_mul _ hρ.ennreal_ofReal hmeas]
    have hpt : ∀ z : Rd d × Y, ((fun z => ENNReal.ofReal (ρ z)) * fun z =>
        ENNReal.ofReal (max (-Real.log (ρ z)) 0)) z ≤
        ENNReal.ofReal (ρ z) * ENNReal.ofReal (r * ‖z.1‖) +
          ENNReal.ofReal (2 * Real.sqrt (g z.1)) := by
      intro z
      simp only [Pi.mul_apply]
      rcases le_or_gt (ρ z) 0 with h | h
      · rw [ENNReal.ofReal_of_nonpos h, zero_mul]; positivity
      · rw [← ENNReal.ofReal_mul h.le, ← ENNReal.ofReal_mul h.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := neg_log_mul_le h (hg0 z.1) (hg1 z.1)
        have h3 : ρ z * (-Real.log (g z.1)) ≤ ρ z * (r * ‖z.1‖) :=
          mul_le_mul_of_nonneg_left (hlg z.1) h.le
        linarith
    calc _ ≤ ∫⁻ z, ENNReal.ofReal (ρ z) * ENNReal.ofReal (r * ‖z.1‖) +
          ENNReal.ofReal (2 * Real.sqrt (g z.1)) ∂(volume.prod m) := lintegral_mono hpt
      _ = ∫⁻ z, ENNReal.ofReal (ρ z) * ENNReal.ofReal (r * ‖z.1‖) ∂(volume.prod m) +
          ∫⁻ z, ENNReal.ofReal (2 * Real.sqrt (g z.1)) ∂(volume.prod m) := by
            apply lintegral_add_right
            exact (Measurable.ennreal_ofReal (by fun_prop))
      _ < ∞ := by
        apply ENNReal.add_lt_top.2 ⟨?_, ?_⟩
        · have hw := lintegral_withDensity_eq_lintegral_mul₀ (μ := volume.prod m)
            hρ.ennreal_ofReal.aemeasurable
            (Measurable.ennreal_ofReal (f := fun z : Rd d × Y => r * ‖z.1‖) (by fun_prop)).aemeasurable
          simp only [Pi.mul_apply] at hw
          rw [← hw, ← hπ]
          exact hnorm.lintegral_lt_top
        · rw [lintegral_prod _ (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable]
          simp only [lintegral_const, measure_univ, mul_one]
          exact hsqi.lintegral_lt_top
  have hnegi : Integrable (fun z => max (-Real.log (ρ z)) 0) π :=
    ⟨(hlogm.neg.max measurable_const).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => le_max_right _ _)).2 hneg⟩
  have hB : Integrable (fun z => |K| * (1 + dist z z1 ^ p) + max (-Real.log (ρ z)) 0) π :=
    (((integrable_const 1).add (integrable_dist_rpow hp hπP z1)).const_mul |K|).add hnegi
  refine hB.mono' hlogm.aestronglyMeasurable ?_
  filter_upwards [hup] with z hz
  rw [Real.norm_eq_abs, abs_le]
  have h0 : 0 ≤ 1 + dist z z1 ^ p := by have := Real.rpow_nonneg (dist_nonneg (x := z) (y := z1)) p; linarith
  have h1 : K * (1 + dist z z1 ^ p) ≤ |K| * (1 + dist z z1 ^ p) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) h0
  have h2 : 0 ≤ |K| * (1 + dist z z1 ^ p) := mul_nonneg (abs_nonneg K) h0
  have h3 := le_max_left (-Real.log (ρ z)) 0
  have h4 := le_max_right (-Real.log (ρ z)) 0
  constructor <;> linarith

/-- Growth upper bound for `log ρ` from the first-order condition. -/
lemma log_dens_upper {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ}
    {F : Measure (Rd d × Y) → ℝ} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ}
    (hA : Assumption21 m p F δF) {η : ℝ} (hη : 0 < η) {π : Measure (Rd d × Y)}
    (hπP : π ∈ Pi (d := d) m p) {ρ : Rd d × Y → ℝ} (hρ : Measurable ρ)
    (hπ : π = (volume.prod m).withDensity (fun z => ENNReal.ofReal (ρ z)))
    (hfoc : ∀ᵐ y ∂m, ∀ x : Rd d, 0 < ρ (x, y) ∧
      DifferentiableAt ℝ (fun x' => Real.log (ρ (x', y))) x ∧
      gradient (fun x' => δF π x' y) x + η • gradient (fun x' => Real.log (ρ (x', y))) x = 0) :
    ∃ K : ℝ, ∃ z1 : Rd d × Y, ∀ᵐ z ∂π, Real.log (ρ z) ≤ K * (1 + dist z z1 ^ p) := by
  obtain ⟨C, y₀, hC⟩ := hA.growth
  have hp0 : (0 : ℝ) ≤ p := by linarith [hA.one_le_p]
  have hC0 : 0 ≤ C := by
    have h := hC π hπP 0 y₀
    have h1 := abs_nonneg (δF π 0 y₀)
    have h2 := Real.rpow_nonneg (dist_nonneg (x := ((0 : Rd d), y₀)) (y := ((0 : Rd d), y₀))) p
    by_contra hneg
    have hneg' := lt_of_not_ge hneg
    nlinarith
  set L : ℝ := η * Real.log ((volume (Metric.closedBall (0 : Rd d) 1)).toReal)⁻¹
  refine ⟨(3 * C + |L|) / η, ((0 : Rd d), y₀), ?_⟩
  have hgood : ∀ᵐ y ∂m, ∀ x : Rd d,
      Real.log (ρ (x, y)) ≤ (3 * C + |L|) / η * (1 + dist (x, y) ((0 : Rd d), y₀) ^ p) := by
    filter_upwards [hfoc, slice_lintegral_eq_one hρ hπ hπP.2.1] with y hy h1 x
    have hc := foc_const_slice (hA.contDiff π hπP y) hy
    have hAy : ∀ x' : Rd d, ‖x'‖ ≤ 1 → δF π x' y ≤ C * (1 + (1 + dist y y₀ ^ p)) := by
      intro x' hx'
      calc δF π x' y ≤ |δF π x' y| := le_abs_self _
        _ ≤ C * (1 + dist (x', y) ((0 : Rd d), y₀) ^ p) := hC π hπP x' y
        _ ≤ C * (1 + (1 + dist y y₀ ^ p)) := by
          have := dist_rpow_le_of_norm_le_one hp0 hx' y y₀
          nlinarith
    have hcu := c_upper_slice hη (g := fun x' => δF π x' y) (ρ := fun x' => ρ (x', y))
      (fun x' => (hy x').1) hc hAy h1.le
    have hDy : dist y y₀ ^ p ≤ dist (x, y) ((0 : Rd d), y₀) ^ p := by
      apply Real.rpow_le_rpow dist_nonneg _ hp0
      rw [Prod.dist_eq]; exact le_max_right _ _
    have hx := hc x
    have hδ : -δF π x y ≤ C * (1 + dist (x, y) ((0 : Rd d), y₀) ^ p) :=
      (neg_le_abs _).trans (hC π hπP x y)
    have hD0 := Real.rpow_nonneg (dist_nonneg (x := (x, y)) (y := ((0 : Rd d), y₀))) p
    have hL := le_abs_self L
    have hmain : η * Real.log (ρ (x, y)) ≤
        (3 * C + |L|) * (1 + dist (x, y) ((0 : Rd d), y₀) ^ p) := by
      have e1 := mul_le_mul_of_nonneg_left hDy hC0
      have e2 := mul_nonneg (add_nonneg hC0 (abs_nonneg L)) hD0
      nlinarith [abs_nonneg L]
    rw [div_mul_eq_mul_div, le_div_iff₀ hη]
    linarith
  have hmap : π.map Prod.snd = m := hπP.2.1
  rw [← hmap] at hgood
  filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hgood] with z hz
  exact hz z.1

end L4b

/-! ## L5: part 2 (first-order condition + convexity ⇒ minimizer) -/

section L5
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma logDens_ae_eq {m : Measure Y} [IsProbabilityMeasure m] {ρ : Rd d × Y → ℝ}
    (hρ : Measurable ρ) {π : Measure (Rd d × Y)}
    (hπ : π = (volume.prod m).withDensity (fun z => ENNReal.ofReal (ρ z))) :
    logDens m π =ᵐ[volume.prod m] fun z => Real.log (max (ρ z) 0) := by
  subst hπ
  filter_upwards [Measure.rnDeriv_withDensity (volume.prod m) hρ.ennreal_ofReal] with z hz
  simp only [logDens, hz, ENNReal.toReal_ofReal']

theorem part2 {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ}
    {F : Measure (Rd d × Y) → ℝ} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ}
    (hA : Assumption21 m p F δF) {η : ℝ} (hη : 0 < η) {πs : Measure (Rd d × Y)}
    (hconv : ConvexOnPi (d := d) m p F) (hπP : πs ∈ Pi (d := d) m p)
    (hfoc : FirstOrderCondition m δF η πs) : IsMinimizer m p F η πs := by
  obtain ⟨ρ, hρ, hπ, hgood⟩ := hfoc
  have hp := hA.one_le_p
  haveI := hπP.1
  obtain ⟨C, y₀, hC⟩ := hA.growth
  have hδm : Measurable (fun z : Rd d × Y => δF πs z.1 z.2) := hA.linDeriv.1 πs hπP
  have hδint : ∀ π' ∈ Pi (d := d) m p, Integrable (fun z : Rd d × Y => δF πs z.1 z.2) π' :=
    fun π' hπ' => integrable_of_growth hp hπ' hδm C ((0 : Rd d), y₀) fun z => hC πs hπP z.1 z.2
  set c : Y → ℝ := fun y => δF πs 0 y + η * Real.log (ρ (0, y)) with hc
  have hcm : Measurable c := by
    have h1 : Measurable (fun y : Y => ((0 : Rd d), y)) := measurable_const.prodMk measurable_id
    exact (hδm.comp h1).add (measurable_const.mul (Real.measurable_log.comp (hρ.comp h1)))
  have hslice : ∀ᵐ y ∂m, ∀ x : Rd d, 0 < ρ (x, y) ∧
      δF πs x y + η * Real.log (ρ (x, y)) = c y := by
    filter_upwards [hgood] with y hy x
    exact ⟨(hy x).1, foc_const_slice (hA.contDiff πs hπP y) hy x⟩
  have htr : ∀ π' ∈ Pi (d := d) m p, ∀ᵐ z ∂π', 0 < ρ z ∧
      δF πs z.1 z.2 + η * Real.log (ρ z) = c z.2 := by
    intro π' hπ'
    have hmap : π'.map Prod.snd = m := hπ'.2.1
    have h := hslice
    rw [← hmap] at h
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable h] with z hz
    exact hz z.1
  obtain ⟨K, z1, hup⟩ := log_dens_upper hA hη hπP hρ hπ hgood
  have hlogs : Integrable (fun z => Real.log (ρ z)) πs :=
    integrable_log_dens hp hπP hρ hπ z1 hup
  have hcint : Integrable c m := by
    have h1 : Integrable (fun z : Rd d × Y => c z.2) πs := by
      refine ((hδint πs hπP).add (hlogs.const_mul η)).congr ?_
      filter_upwards [htr πs hπP] with z hz
      exact hz.2
    rw [← hπP.2.1]
    exact (integrable_map_measure hcm.aestronglyMeasurable measurable_snd.aemeasurable).2 h1
  have hkey : ∀ π' ∈ Pi (d := d) m p, Integrable (fun z => Real.log (ρ z)) π' ∧
      ∫ z, δF πs z.1 z.2 ∂π' + η * ∫ z, Real.log (ρ z) ∂π' = ∫ y, c y ∂m := by
    intro π' hπ'
    have hcz : Integrable (fun z : Rd d × Y => c z.2) π' := by
      have h := hcint
      rw [← hπ'.2.1] at h
      exact (integrable_map_measure hcm.aestronglyMeasurable measurable_snd.aemeasurable).1 h
    have hlog' : Integrable (fun z => Real.log (ρ z)) π' := by
      refine ((hcz.sub (hδint π' hπ')).div_const η).congr ?_
      filter_upwards [htr π' hπ'] with z hz
      simp only [Pi.sub_apply]
      rw [div_eq_iff hη.ne']
      linarith [hz.2, mul_comm η (Real.log (ρ z))]
    refine ⟨hlog', ?_⟩
    rw [← integral_const_mul, ← integral_add (hδint π' hπ') (hlog'.const_mul η), ← hπ'.2.1,
      integral_map measurable_snd.aemeasurable hcm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [htr π' hπ'] with z hz
    exact hz.2
  have hac : πs ≪ volume.prod m := by rw [hπ]; exact withDensity_absolutelyContinuous _ _
  have hld : logDens m πs =ᵐ[πs] fun z => Real.log (ρ z) := by
    filter_upwards [hac.ae_eq (logDens_ae_eq hρ hπ), htr πs hπP] with z hz hz'
    rw [hz, max_eq_left hz'.1.le]
  have hrel : relEnt m πs = ((∫ z, Real.log (ρ z) ∂πs : ℝ) : EReal) := by
    rw [relEnt, if_pos ⟨hac, hlogs.congr hld.symm⟩, integral_congr_ae hld]
  have hpos0 : ∀ᵐ z ∂(volume.prod m), 0 < ρ z := by
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hρ)]
    refine ae_of_all _ fun x => ?_
    filter_upwards [hslice] with y hy
    exact (hy x).1
  have hne0 : ∀ᵐ z ∂(volume.prod m), ENNReal.ofReal (ρ z) ≠ 0 := by
    filter_upwards [hpos0] with z hz
    exact (ENNReal.ofReal_pos.2 hz).ne'
  have hacs : volume.prod m ≪ πs := by
    rw [hπ]
    exact withDensity_absolutelyContinuous' hρ.ennreal_ofReal.aemeasurable hne0
  refine ⟨hπP, fun π' hπ' => ?_⟩
  haveI := hπ'.1
  by_cases hfin : π' ≪ volume.prod m ∧ Integrable (logDens m π') π'
  swap
  · have htop : relEnt m π' = ⊤ := by rw [relEnt, if_neg hfin]
    unfold V
    rw [htop, EReal.coe_mul_top_of_pos hη, EReal.coe_add_top]
    exact le_top
  have hrel' : relEnt m π' = ((∫ z, logDens m π' z ∂π' : ℝ) : EReal) := by
    rw [relEnt, if_pos hfin]
  have hgibbs : ∫ z, Real.log (ρ z) ∂π' ≤ ∫ z, logDens m π' z ∂π' := by
    have hac' : π' ≪ πs := hfin.1.trans hacs
    have hrn := Measure.rnDeriv_withDensity_right π' (volume.prod m)
      hρ.ennreal_ofReal.aemeasurable hne0 (ae_of_all _ fun z => ENNReal.ofReal_ne_top)
    rw [← hπ] at hrn
    have hllr : llr π' πs =ᵐ[π'] fun z => logDens m π' z - Real.log (ρ z) := by
      filter_upwards [hfin.1.ae_eq hrn, hfin.1.ae_le hpos0, Measure.rnDeriv_pos hfin.1,
        hfin.1.ae_le (Measure.rnDeriv_lt_top π' (volume.prod m))] with z h1 h2 h3 h4
      show Real.log ((π'.rnDeriv πs z).toReal) =
        Real.log ((π'.rnDeriv (volume.prod m) z).toReal) - Real.log (ρ z)
      rw [h1, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal h2.le,
        Real.log_mul (inv_ne_zero h2.ne') (ENNReal.toReal_pos h3.ne' h4.ne).ne', Real.log_inv]
      ring
    have hint : Integrable (llr π' πs) π' :=
      (hfin.2.sub (hkey π' hπ').1).congr hllr.symm
    have h := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac' hint
    rw [integral_congr_ae hllr, integral_sub hfin.2 (hkey π' hπ').1] at h
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at h
    linarith
  unfold V
  rw [hrel, hrel', ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  have hc1 := (hkey πs hπP).2
  have hc2 := (hkey π' hπ').2
  have hcv := pairDiff_le_of_convex hA hconv hπP hπ'
  unfold pairDiff at hcv
  have hg := mul_le_mul_of_nonneg_left hgibbs hη.le
  linarith

end L5


/-! ## L6A (step A): a reference measure in `Π` with finite entropy and positive density -/

section L6A
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma max_rpow_le_add {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    max a b ^ p ≤ a ^ p + b ^ p := by
  have h1 := Real.rpow_nonneg ha p
  have h2 := Real.rpow_nonneg hb p
  rcases le_total a b with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

lemma ref_measure {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ} (hp : 1 ≤ p)
    {π : Measure (Rd d × Y)} (hπP : π ∈ Pi (d := d) m p) :
    ∃ g : Rd d → ℝ, Measurable g ∧ (∀ x, 0 < g x) ∧
      (volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1)) ∈ Pi (d := d) m p ∧
      Integrable (fun z : Rd d × Y => Real.log (g z.1))
        ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))) ∧
      (∃ C : ℝ, ∃ z1 : Rd d × Y, ∀ z : Rd d × Y, |Real.log (g z.1)| ≤ C * (1 + dist z z1 ^ p)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hp0 : (0 : ℝ) ≤ p := by linarith
  set r : ℝ := (d : ℝ) + p + 1 with hr
  have hr0 : 0 < r := by linarith
  set g0 : Rd d → ℝ := fun x => (1 + ‖x‖) ^ (-r) with hg0
  have hg0pos : ∀ x, 0 < g0 x := fun x => Real.rpow_pos_of_pos (by positivity) _
  have hg0m : Measurable g0 := (measurable_const.add measurable_norm).pow_const _
  have hint : Integrable g0 volume :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; linarith)
  set K : ℝ := ∫ x, g0 x with hK
  have hKpos : 0 < K := by
    rw [hK, integral_pos_iff_support_of_nonneg (fun x => (hg0pos x).le) hint]
    have : Function.support g0 = Set.univ := Set.eq_univ_of_forall fun x => (hg0pos x).ne'
    rw [this]
    exact Measure.measure_univ_pos.2 (NeZero.ne _)
  set g : Rd d → ℝ := fun x => g0 x / K with hg
  have hgpos : ∀ x, 0 < g x := fun x => div_pos (hg0pos x) hKpos
  have hgm : Measurable g := hg0m.div_const K
  have hgint : Integrable g volume := hint.div_const K
  set ν1 : Measure (Rd d) := volume.withDensity (fun x => ENNReal.ofReal (g x)) with hν1
  have hν1prob : IsProbabilityMeasure ν1 := by
    constructor
    have h1 : ∫ x, g x = 1 := by
      simp only [hg]; rw [integral_div, ← hK, div_self hKpos.ne']
    rw [hν1, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hgint (ae_of_all _ fun x => (hgpos x).le), h1,
      ENNReal.ofReal_one]
  have hν0 : (volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1)) = ν1.prod m :=
    (prod_withDensity_left hgm.ennreal_ofReal).symm
  haveI := hπP.1
  obtain ⟨-, hmarg, z0, hmom⟩ := hπP
  set z0' : Rd d × Y := ((0 : Rd d), z0.2) with hz0'
  have hmomπ := moment_lt_top_of_base hp z0 z0' hmom
  -- moment of `m`
  have hmomm : ∫⁻ y, ENNReal.ofReal (dist y z0.2 ^ p) ∂m < ∞ := by
    have hmeas : Measurable (fun y : Y => ENNReal.ofReal (dist y z0.2 ^ p)) :=
      ((measurable_id.dist measurable_const).pow_const p).ennreal_ofReal
    rw [← hmarg, lintegral_map hmeas measurable_snd]
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hmomπ
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow dist_nonneg _ hp0
    rw [Prod.dist_eq]; exact le_max_right _ _
  -- moment of `ν1`
  have hmom1 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ p) ∂ν1 < ∞ := by
    have hmeas : Measurable (fun x : Rd d => ENNReal.ofReal (‖x‖ ^ p)) :=
      (measurable_norm.pow_const p).ennreal_ofReal
    rw [hν1, lintegral_withDensity_eq_lintegral_mul _ hgm.ennreal_ofReal hmeas]
    have hb : Integrable (fun x : Rd d => (1 + ‖x‖) ^ (-((d : ℝ) + 1)) / K) volume :=
      (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; linarith)).div_const K
    have hi : Integrable (fun x : Rd d => g x * ‖x‖ ^ p) volume := by
      refine hb.mono' (hgm.mul (measurable_norm.pow_const p)).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      have h1 : 0 < 1 + ‖x‖ := by positivity
      have hn := Real.rpow_nonneg (norm_nonneg x) p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hgpos x).le hn)]
      show g0 x / K * ‖x‖ ^ p ≤ (1 + ‖x‖) ^ (-((d : ℝ) + 1)) / K
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hKpos.le
      calc g0 x * ‖x‖ ^ p ≤ (1 + ‖x‖) ^ (-r) * (1 + ‖x‖) ^ p :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (norm_nonneg x) (by linarith) hp0) (hg0pos x).le
        _ = (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
            rw [← Real.rpow_add h1]; congr 1; rw [hr]; ring
    have := hi.lintegral_lt_top
    refine lt_of_le_of_lt (le_of_eq ?_) this
    apply lintegral_congr; intro x
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hgpos x).le]
  have hP : ν1.prod m ∈ Pi (d := d) m p := by
    refine ⟨inferInstance, ?_, z0', ?_⟩
    · rw [Measure.map_snd_prod, measure_univ, one_smul]
    · have hbd : ∀ z : Rd d × Y, ENNReal.ofReal (dist z z0' ^ p) ≤
          ENNReal.ofReal (‖z.1‖ ^ p) + ENNReal.ofReal (dist z.2 z0.2 ^ p) := by
        intro z
        rw [← ENNReal.ofReal_add (Real.rpow_nonneg (norm_nonneg _) p)
          (Real.rpow_nonneg dist_nonneg p)]
        apply ENNReal.ofReal_le_ofReal
        rw [hz0', Prod.dist_eq, dist_zero_right]
        exact max_rpow_le_add (norm_nonneg _) dist_nonneg hp0
      have m1 : Measurable (fun x : Rd d => ENNReal.ofReal (‖x‖ ^ p)) :=
        (measurable_norm.pow_const p).ennreal_ofReal
      have m2 : Measurable (fun y : Y => ENNReal.ofReal (dist y z0.2 ^ p)) :=
        ((measurable_id.dist measurable_const).pow_const p).ennreal_ofReal
      calc ∫⁻ z, ENNReal.ofReal (dist z z0' ^ p) ∂(ν1.prod m)
          ≤ ∫⁻ z, ENNReal.ofReal (‖z.1‖ ^ p) + ENNReal.ofReal (dist z.2 z0.2 ^ p) ∂(ν1.prod m) :=
            lintegral_mono hbd
        _ = ∫⁻ z, ENNReal.ofReal (‖z.1‖ ^ p) ∂(ν1.prod m) +
            ∫⁻ z, ENNReal.ofReal (dist z.2 z0.2 ^ p) ∂(ν1.prod m) :=
            lintegral_add_left (m1.comp measurable_fst) _
        _ = ∫⁻ x, ENNReal.ofReal (‖x‖ ^ p) ∂ν1 + ∫⁻ y, ENNReal.ofReal (dist y z0.2 ^ p) ∂m := by
            rw [← lintegral_map m1 measurable_fst, ← lintegral_map m2 measurable_snd,
              Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, measure_univ,
              one_smul, one_smul]
        _ < ∞ := ENNReal.add_lt_top.2 ⟨hmom1, hmomm⟩
  have hbound_aux : ∀ z : Rd d × Y, |Real.log (g z.1)| ≤ (r + |Real.log K|) * (1 + dist z z0' ^ p) := by
    intro z
    have h1 : 0 < 1 + ‖z.1‖ := by positivity
    have hl : Real.log (g z.1) = -r * Real.log (1 + ‖z.1‖) - Real.log K := by
      show Real.log (g0 z.1 / K) = _
      rw [Real.log_div (hg0pos z.1).ne' hKpos.ne']
      show Real.log ((1 + ‖z.1‖) ^ (-r)) - Real.log K = _
      rw [Real.log_rpow h1]
    have hl0 : 0 ≤ Real.log (1 + ‖z.1‖) := Real.log_nonneg (by linarith [norm_nonneg z.1])
    have hl1 : Real.log (1 + ‖z.1‖) ≤ ‖z.1‖ := by
      have := Real.log_le_sub_one_of_pos h1; linarith
    have hn : ‖z.1‖ ≤ 1 + dist z z0' ^ p := by
      have : ‖z.1‖ ≤ dist z z0' := by
        rw [hz0', Prod.dist_eq, dist_zero_right]; exact le_max_left _ _
      exact this.trans (le_one_add_rpow dist_nonneg hp)
    have hD : 0 ≤ dist z z0' ^ p := Real.rpow_nonneg dist_nonneg p
    rw [hl, abs_le]
    have hLK := abs_nonneg (Real.log K)
    have hLK1 := neg_abs_le (Real.log K)
    have hLK2 := le_abs_self (Real.log K)
    constructor <;> nlinarith
  have hbound : ∀ z : Rd d × Y, |Real.log (g z.1)| ≤ (r + |Real.log K|) * (1 + dist z z0' ^ p) := by
    intro z
    exact hbound_aux z
  refine ⟨g, hgm, hgpos, by rwa [hν0], ?_, ⟨_, z0', hbound⟩⟩
  rw [hν0]
  exact integrable_of_growth hp hP (Real.measurable_log.comp (hgm.comp measurable_fst))
    (r + |Real.log K|) z0' hbound

end L6A

/-! ## L6B (step A'): a minimizer has finite entropy, hence a density -/

section L6B
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma relEnt_withDensity_ne_top {m : Measure Y} [IsProbabilityMeasure m] {g : Rd d → ℝ}
    (hg : Measurable g) (hgpos : ∀ x, 0 < g x)
    (hint : Integrable (fun z : Rd d × Y => Real.log (g z.1))
        ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1)))) :
    relEnt m ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))) ≠ ⊤ := by
  have hρ : Measurable (fun z : Rd d × Y => g z.1) := hg.comp measurable_fst
  have hae := logDens_ae_eq (m := m) hρ rfl
  have hac : (volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1)) ≪ volume.prod m :=
    withDensity_absolutelyContinuous _ _
  have hae' := hac.ae_le hae
  have hint' : Integrable (logDens m ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))))
      ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))) := by
    refine hint.congr ?_
    filter_upwards [hae'] with z hz
    rw [hz]
    simp only [max_eq_left (hgpos z.1).le]
  unfold relEnt
  rw [if_pos ⟨hac, hint'⟩]
  exact EReal.coe_ne_top _

lemma minimizer_ac {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ} (hp : 1 ≤ p)
    {F : Measure (Rd d × Y) → ℝ} {η : ℝ} (hη : 0 < η) {πs : Measure (Rd d × Y)}
    (hmin : IsMinimizer m p F η πs) :
    πs ≪ volume.prod m ∧ Integrable (logDens m πs) πs := by
  obtain ⟨g, hg, hgpos, hν0, hint, -⟩ := ref_measure hp hmin.1
  have hfin := relEnt_withDensity_ne_top (m := m) hg hgpos hint
  have hle := hmin.2 _ hν0
  by_contra hcon
  have htop : relEnt m πs = ⊤ := by
    unfold relEnt
    rw [if_neg hcon]
  obtain ⟨r, hr⟩ : ∃ r : ℝ,
      relEnt m ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))) = r := by
    unfold relEnt at hfin ⊢
    split_ifs at hfin ⊢ with h
    · exact ⟨_, rfl⟩
    · exact absurd rfl hfin
  unfold V at hle
  rw [htop, hr, EReal.mul_top_of_pos (by exact_mod_cast hη), EReal.coe_add_top] at hle
  have hne : ((F ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))) : EReal)
      + (η : EReal) * (r : EReal)) ≠ ⊤ := by
    rw [← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_ne_top _
  exact hne (top_le_iff.mp hle)

lemma eq_withDensity_rnDeriv {m : Measure Y} [IsProbabilityMeasure m] {πs : Measure (Rd d × Y)}
    [IsFiniteMeasure πs] (hac : πs ≪ volume.prod m) :
    πs = (volume.prod m).withDensity
      (fun z => ENNReal.ofReal ((πs.rnDeriv (volume.prod m) z).toReal)) := by
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hac]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top πs (volume.prod m)] with z hz
  rw [ENNReal.ofReal_toReal hz.ne]

end L6B

/-! ## L6C (step B): the first variation along admissible perturbations vanishes -/

section L6C
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma one_add_pos_of_abs_le {u : ℝ} (hu : |u| ≤ 1 / 2) : 0 < 1 + u := by
  rw [abs_le] at hu; linarith

lemma abs_log_one_add_le {u : ℝ} (hu : |u| ≤ 1 / 2) : |Real.log (1 + u)| ≤ 1 := by
  have h1 := one_add_pos_of_abs_le hu
  rw [abs_le] at hu ⊢
  have hup := Real.log_le_sub_one_of_pos h1
  have hlo := Real.one_sub_inv_le_log_of_pos h1
  have hinv : (1 + u)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ h1]; linarith
  constructor <;> linarith

lemma one_add_mul_log_le {u : ℝ} (hu : 0 < 1 + u) : (1 + u) * Real.log (1 + u) ≤ u + u ^ 2 := by
  have h := Real.log_le_sub_one_of_pos hu
  have h2 : (1 + u) * Real.log (1 + u) ≤ (1 + u) * u := by
    apply mul_le_mul_of_nonneg_left _ hu.le; linarith
  nlinarith

lemma integrable_bdd_mul {πs : Measure (Rd d × Y)} {h g : Rd d × Y → ℝ} (hm : Measurable h)
    (hb : ∀ z, |h z| ≤ 1 / 2) (hg : Integrable g πs) {c : ℝ} :
    Integrable (fun z => (c + h z) * g z) πs := by
  refine (hg.norm.const_mul (|c| + 1 / 2)).mono'
    (((measurable_const.add hm).aestronglyMeasurable).mul hg.aestronglyMeasurable)
    (ae_of_all _ fun z => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (by linarith [hb z])) (norm_nonneg _)

lemma integrable_of_abs_le {πs : Measure (Rd d × Y)} [IsFiniteMeasure πs] {g : Rd d × Y → ℝ}
    (hg : AEStronglyMeasurable g πs) {C : ℝ} (hC : ∀ z, |g z| ≤ C) : Integrable g πs :=
  (integrable_const C).mono' hg (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC z)

lemma integral_pert {πs : Measure (Rd d × Y)} {h : Rd d × Y → ℝ} (hm : Measurable h)
    (hb : ∀ z, |h z| ≤ 1 / 2) (g : Rd d × Y → ℝ) :
    ∫ z, g z ∂(πs.withDensity (fun z => ENNReal.ofReal (1 + h z)))
      = ∫ z, (1 + h z) * g z ∂πs := by
  have hf : Measurable (fun z => (1 + h z).toNNReal) := (measurable_const.add hm).real_toNNReal
  have e := integral_withDensity_eq_integral_smul (μ := πs) hf g
  rw [show (fun z => ENNReal.ofReal (1 + h z)) = fun z => (((1 + h z).toNNReal : NNReal) : ℝ≥0∞)
    from rfl, e]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (one_add_pos_of_abs_le (hb z)).le]

lemma integrable_pert {πs : Measure (Rd d × Y)} {h : Rd d × Y → ℝ} (hm : Measurable h)
    (hb : ∀ z, |h z| ≤ 1 / 2) {g : Rd d × Y → ℝ} (hg : Integrable g πs) :
    Integrable g (πs.withDensity (fun z => ENNReal.ofReal (1 + h z))) := by
  have hf : Measurable (fun z => (1 + h z).toNNReal) := (measurable_const.add hm).real_toNNReal
  rw [show (fun z => ENNReal.ofReal (1 + h z)) = fun z => (((1 + h z).toNNReal : NNReal) : ℝ≥0∞)
    from rfl, integrable_withDensity_iff_integrable_smul hf]
  refine (integrable_bdd_mul (c := 1) hm hb hg).congr (ae_of_all _ fun z => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (one_add_pos_of_abs_le (hb z)).le]

lemma pert_mem_Pi {m : Measure Y} {p : ℝ} {πs : Measure (Rd d × Y)}
    (hπP : πs ∈ Pi (d := d) m p) {h : Rd d × Y → ℝ} (hm : Measurable h) (hb : ∀ z, |h z| ≤ 1 / 2)
    (hadm : ∀ A : Set Y, MeasurableSet A → ∫ z in Prod.snd ⁻¹' A, h z ∂πs = 0) :
    πs.withDensity (fun z => ENNReal.ofReal (1 + h z)) ∈ Pi (d := d) m p := by
  haveI := hπP.1
  have hhint : Integrable h πs := integrable_of_abs_le hm.aestronglyMeasurable hb
  have hI : Integrable (fun z => 1 + h z) πs := (integrable_const 1).add hhint
  have hS : ∀ A : Set Y, MeasurableSet A →
      πs.withDensity (fun z => ENNReal.ofReal (1 + h z)) (Prod.snd ⁻¹' A) = πs (Prod.snd ⁻¹' A) := by
    intro A hA
    have hA' : MeasurableSet (Prod.snd ⁻¹' A : Set (Rd d × Y)) := measurable_snd hA
    rw [withDensity_apply _ hA', ← ofReal_integral_eq_lintegral_ofReal hI.integrableOn
      (ae_of_all _ fun z => (one_add_pos_of_abs_le (hb z)).le),
      integral_add (integrable_const _).integrableOn hhint.integrableOn, hadm A hA, add_zero,
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · have := hS Set.univ MeasurableSet.univ
    rw [Set.preimage_univ] at this
    rw [this]; exact measure_univ
  · ext A hA
    rw [Measure.map_apply measurable_snd hA, hS A hA, ← Measure.map_apply measurable_snd hA, hπP.2.1]
  · obtain ⟨z0, hz0⟩ := hπP.2.2
    refine ⟨z0, ?_⟩
    have hfm : Measurable (fun z => ENNReal.ofReal (1 + h z)) :=
      (measurable_const.add hm).ennreal_ofReal
    rw [lintegral_withDensity_eq_lintegral_mul _ hfm (measurable_dist_rpow p z0).ennreal_ofReal]
    calc ∫⁻ z, ((fun z => ENNReal.ofReal (1 + h z)) * fun z => ENNReal.ofReal (dist z z0 ^ p)) z ∂πs
        ≤ ∫⁻ z, ENNReal.ofReal 2 * ENNReal.ofReal (dist z z0 ^ p) ∂πs := by
          refine lintegral_mono fun z => ?_
          simp only [Pi.mul_apply]
          have := hb z; rw [abs_le] at this
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
      _ = ENNReal.ofReal 2 * ∫⁻ z, ENNReal.ofReal (dist z z0 ^ p) ∂πs :=
          lintegral_const_mul _ (measurable_dist_rpow p z0).ennreal_ofReal
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hz0

lemma mix_pert {πs : Measure (Rd d × Y)} {h : Rd d × Y → ℝ} (hm : Measurable h)
    (hb : ∀ z, |h z| ≤ 1 / 2) {ε : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1) :
    mix ε πs (πs.withDensity (fun z => ENNReal.ofReal (1 + h z)))
      = πs.withDensity (fun z => ENNReal.ofReal (1 + ε * h z)) := by
  have hfm : Measurable (fun z => ENNReal.ofReal (1 + h z)) := (measurable_const.add hm).ennreal_ofReal
  unfold mix
  rw [← withDensity_smul _ hfm, ← withDensity_const, ← withDensity_add_left measurable_const]
  refine withDensity_congr_ae (ae_of_all _ fun z => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hε.1, ← ENNReal.ofReal_add (by linarith [hε.2])
    (mul_nonneg hε.1 (one_add_pos_of_abs_le (hb z)).le)]
  congr 1; ring

lemma relEnt_pert {m : Measure Y} [IsProbabilityMeasure m] {πs : Measure (Rd d × Y)}
    [IsProbabilityMeasure πs] (hac : πs ≪ volume.prod m) (hint : Integrable (logDens m πs) πs)
    {h : Rd d × Y → ℝ} (hm : Measurable h) (hb : ∀ z, |h z| ≤ 1 / 2) :
    relEnt m (πs.withDensity (fun z => ENNReal.ofReal (1 + h z)))
      = ((∫ z, logDens m πs z ∂πs + ∫ z, h z * logDens m πs z ∂πs
          + ∫ z, (1 + h z) * Real.log (1 + h z) ∂πs : ℝ) : EReal) := by
  have h1 : ∀ z, 0 < 1 + h z := fun z => one_add_pos_of_abs_le (hb z)
  have hfm : Measurable (fun z => ENNReal.ofReal (1 + h z)) := (measurable_const.add hm).ennreal_ofReal
  have hνac : πs.withDensity (fun z => ENNReal.ofReal (1 + h z)) ≪ volume.prod m :=
    (withDensity_absolutelyContinuous _ _).trans hac
  have hrn := Measure.rnDeriv_withDensity_left (μ := πs) (ν := volume.prod m) hfm.aemeasurable
    (ae_of_all _ fun z => ENNReal.ofReal_ne_top)
  have hll : logDens m (πs.withDensity (fun z => ENNReal.ofReal (1 + h z)))
      =ᵐ[πs] fun z => Real.log (1 + h z) + logDens m πs z := by
    filter_upwards [hac.ae_le hrn, Measure.rnDeriv_pos hac,
      hac.ae_le (Measure.rnDeriv_lt_top πs (volume.prod m))] with z hz hpos hlt
    simp only [logDens, hz, ENNReal.toReal_mul, ENNReal.toReal_ofReal (h1 z).le]
    rw [Real.log_mul (h1 z).ne' (ENNReal.toReal_pos hpos.ne' hlt.ne).ne']
  have hLm : Measurable (fun z => Real.log (1 + h z)) := Real.measurable_log.comp (measurable_const.add hm)
  have hL : Integrable (fun z => Real.log (1 + h z)) πs :=
    integrable_of_abs_le hLm.aestronglyMeasurable fun z => abs_log_one_add_le (hb z)
  have hhD : Integrable (fun z => h z * logDens m πs z) πs := by
    have := integrable_bdd_mul (c := 0) hm hb hint
    simpa only [zero_add] using this
  have hLL : Integrable (fun z => (1 + h z) * Real.log (1 + h z)) πs := integrable_bdd_mul (c := 1) hm hb hL
  have hintν' : Integrable (logDens m (πs.withDensity (fun z => ENNReal.ofReal (1 + h z)))) πs :=
    (hL.add hint).congr hll.symm
  have hintν := integrable_pert hm hb hintν'
  unfold relEnt
  rw [if_pos ⟨hνac, hintν⟩, integral_pert hm hb]
  congr 1
  have hsum : Integrable (fun z => logDens m πs z + h z * logDens m πs z) πs := hint.add hhD
  rw [← integral_add hint hhD, ← integral_add hsum hLL]
  refine integral_congr_ae ?_
  filter_upwards [hll] with z hz
  rw [hz]; ring

end L6C

/-! ## L6D (step B): first variation of a minimizer -/

section L6D
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma first_variation_nonneg {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ}
    {F : Measure (Rd d × Y) → ℝ} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ}
    (hA : Assumption21 m p F δF) {η : ℝ} (hη : 0 < η) {πs : Measure (Rd d × Y)}
    (hmin : IsMinimizer m p F η πs) {h : Rd d × Y → ℝ} (hm : Measurable h)
    (hb : ∀ z, |h z| ≤ 1 / 2)
    (hadm : ∀ A : Set Y, MeasurableSet A → ∫ z in Prod.snd ⁻¹' A, h z ∂πs = 0) :
    0 ≤ ∫ z, δF πs z.1 z.2 * h z ∂πs + η * ∫ z, h z * logDens m πs z ∂πs := by
  have hπP := hmin.1
  haveI := hπP.1
  have hp := hA.one_le_p
  obtain ⟨hac, hint⟩ := minimizer_ac hp hη hmin
  obtain ⟨C, y₀, hC⟩ := hA.growth
  have hδm : Measurable (fun z : Rd d × Y => δF πs z.1 z.2) := hA.linDeriv.1 πs hπP
  have hδint : Integrable (fun z : Rd d × Y => δF πs z.1 z.2) πs :=
    integrable_of_growth hp hπP hδm C ((0 : Rd d), y₀) fun z => hC πs hπP z.1 z.2
  have hhint : Integrable h πs := integrable_of_abs_le hm.aestronglyMeasurable hb
  have hh0 : ∫ z, h z ∂πs = 0 := by
    have := hadm Set.univ MeasurableSet.univ
    rwa [Set.preimage_univ, Measure.restrict_univ] at this
  set I : ℝ := ∫ z, h z * logDens m πs z ∂πs with hI
  set H : ℝ := ∫ z, logDens m πs z ∂πs with hH
  have hπfin : relEnt m πs = (H : EReal) := by
    unfold relEnt; rw [if_pos ⟨hac, hint⟩]
  have hνP := pert_mem_Pi hπP hm hb hadm
  have key : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      0 ≤ (F (mix ε πs (πs.withDensity (fun z => ENNReal.ofReal (1 + h z)))) - F πs) / ε
        + η * I + η * ε / 4 := by
    intro ε hε
    have hε0 := hε.1
    have hεI : ε ∈ Set.Icc (0 : ℝ) 1 := ⟨hε.1.le, hε.2⟩
    have hbε : ∀ z, |ε * h z| ≤ 1 / 2 := fun z => by
      rw [abs_mul, abs_of_pos hε0]
      calc ε * |h z| ≤ 1 * |h z| := mul_le_mul_of_nonneg_right hε.2 (abs_nonneg _)
        _ ≤ 1 / 2 := by rw [one_mul]; exact hb z
    have hmε : Measurable (fun z => ε * h z) := measurable_const.mul hm
    have hmixP := mix_mem_Pi hp hπP hνP hεI
    have hle := hmin.2 _ hmixP
    rw [mix_pert hm hb hεI] at hle hmixP
    unfold V at hle
    rw [hπfin, relEnt_pert hac hint hmε hbε, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
    have hI2 : ∫ z, ε * h z * logDens m πs z ∂πs = ε * I := by
      rw [hI, ← integral_const_mul]; congr 1; funext z; ring
    have hLm : Measurable (fun z => Real.log (1 + ε * h z)) :=
      Real.measurable_log.comp (measurable_const.add hmε)
    have hL : Integrable (fun z => Real.log (1 + ε * h z)) πs :=
      integrable_of_abs_le hLm.aestronglyMeasurable fun z => abs_log_one_add_le (hbε z)
    have hLL : Integrable (fun z => (1 + ε * h z) * Real.log (1 + ε * h z)) πs :=
      integrable_bdd_mul (c := 1) hmε hbε hL
    have hJ : ∫ z, (1 + ε * h z) * Real.log (1 + ε * h z) ∂πs ≤ ε ^ 2 / 4 := by
      calc ∫ z, (1 + ε * h z) * Real.log (1 + ε * h z) ∂πs
          ≤ ∫ z, (ε * h z + ε ^ 2 / 4) ∂πs := by
            refine integral_mono hLL ((hhint.const_mul ε).add (integrable_const _)) fun z => ?_
            have h1 := one_add_mul_log_le (one_add_pos_of_abs_le (hbε z))
            have h2 : (ε * h z) ^ 2 ≤ ε ^ 2 / 4 := by
              have hz := hb z
              have h4 : (h z) ^ 2 ≤ 1 / 4 := by
                rw [← sq_abs]; nlinarith [abs_nonneg (h z)]
              have h3 : (ε * h z) ^ 2 = ε ^ 2 * (h z) ^ 2 := by ring
              rw [h3]; nlinarith [sq_nonneg ε]
            simp only; linarith
        _ = ε ^ 2 / 4 := by
            rw [integral_add (hhint.const_mul ε) (integrable_const _), integral_const_mul, hh0]
            simp
    rw [hI2] at hle
    have hq : (F (πs.withDensity (fun z => ENNReal.ofReal (1 + ε * h z))) - F πs) / ε
        + η * I + η * ε / 4
        = (F (πs.withDensity (fun z => ENNReal.ofReal (1 + ε * h z))) - F πs
            + η * (ε * I) + η * (ε ^ 2 / 4)) / ε := by
      field_simp
    rw [mix_pert hm hb hεI, hq]
    refine div_nonneg ?_ hε0.le
    have hJη := mul_le_mul_of_nonneg_left hJ hη.le
    nlinarith
  have hlim := tendsto_slope_F hA hπP hνP
  have hlim2 : Tendsto (fun ε => (F (mix ε πs (πs.withDensity (fun z => ENNReal.ofReal (1 + h z))))
        - F πs) / ε + η * I + η * ε / 4) (𝓝[>] 0)
      (𝓝 (pairDiff (fun z => δF πs z.1 z.2) πs (πs.withDensity (fun z => ENNReal.ofReal (1 + h z)))
        + η * I + η * 0 / 4)) := by
    refine (hlim.add tendsto_const_nhds).add ?_
    exact ((tendsto_const_nhds.mul tendsto_id).div_const 4).mono_left nhdsWithin_le_nhds
  have hge := ge_of_tendsto hlim2
    (Filter.mem_of_superset (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) fun ε hε => key ε hε)
  have hpd : pairDiff (fun z => δF πs z.1 z.2) πs (πs.withDensity (fun z => ENNReal.ofReal (1 + h z)))
      = ∫ z, δF πs z.1 z.2 * h z ∂πs := by
    unfold pairDiff
    rw [integral_pert hm hb, ← integral_sub (integrable_bdd_mul (c := 1) hm hb hδint) hδint]
    congr 1; funext z; ring
  rw [hpd] at hge
  linarith

lemma first_variation_eq_zero {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ}
    {F : Measure (Rd d × Y) → ℝ} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ}
    (hA : Assumption21 m p F δF) {η : ℝ} (hη : 0 < η) {πs : Measure (Rd d × Y)}
    (hmin : IsMinimizer m p F η πs) {h : Rd d × Y → ℝ} (hm : Measurable h)
    (hb : ∀ z, |h z| ≤ 1 / 2)
    (hadm : ∀ A : Set Y, MeasurableSet A → ∫ z in Prod.snd ⁻¹' A, h z ∂πs = 0) :
    ∫ z, δF πs z.1 z.2 * h z ∂πs + η * ∫ z, h z * logDens m πs z ∂πs = 0 := by
  have h1 := first_variation_nonneg hA hη hmin hm hb hadm
  have h2 := first_variation_nonneg hA hη hmin (h := fun z => -h z) hm.neg
    (fun z => by rw [abs_neg]; exact hb z)
    (fun A hA' => by rw [integral_neg, hadm A hA', neg_zero])
  have e1 : ∫ z, δF πs z.1 z.2 * -h z ∂πs = -∫ z, δF πs z.1 z.2 * h z ∂πs := by
    rw [← integral_neg]; congr 1; funext z; ring
  have e2 : ∫ z, -h z * logDens m πs z ∂πs = -∫ z, h z * logDens m πs z ∂πs := by
    rw [← integral_neg]; congr 1; funext z; ring
  rw [e1, e2] at h2
  linarith

end L6D

/-! ## L6E (step C): `Ξ` is a function of `y` only -/

section L6E
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma clamp_abs_le (t : ℝ) : |max (-(1 / 4 : ℝ)) (min (1 / 4) t)| ≤ 1 / 4 := by
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma mul_clamp_pos {t : ℝ} (ht : t ≠ 0) : 0 < t * max (-(1 / 4 : ℝ)) (min (1 / 4) t) := by
  rcases lt_or_gt_of_ne ht with h | h
  · have : max (-(1 / 4 : ℝ)) (min (1 / 4) t) < 0 :=
      max_lt (by norm_num) (lt_of_le_of_lt (min_le_right _ _) h)
    nlinarith
  · have : 0 < max (-(1 / 4 : ℝ)) (min (1 / 4) t) :=
      lt_of_lt_of_le (lt_min (by norm_num) h) (le_max_right _ _)
    nlinarith

lemma mul_clamp_nonneg (t : ℝ) : 0 ≤ t * max (-(1 / 4 : ℝ)) (min (1 / 4) t) := by
  rcases eq_or_ne t 0 with h | h
  · simp [h]
  · exact (mul_clamp_pos h).le

lemma clamp_continuous : Continuous (fun t : ℝ => max (-(1 / 4 : ℝ)) (min (1 / 4) t)) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma integrable_mul_bdd {πs : Measure (Rd d × Y)} {g b : Rd d × Y → ℝ} (hg : Integrable g πs)
    (hb : AEStronglyMeasurable b πs) {C : ℝ} (hC : ∀ z, |b z| ≤ C) :
    Integrable (fun z => b z * g z) πs := by
  refine (hg.norm.const_mul C).mono' (hb.mul hg.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)

lemma ae_eq_comp_snd_of_orth {πs : Measure (Rd d × Y)} [IsProbabilityMeasure πs]
    {X : Rd d × Y → ℝ} (hXm : Measurable X) (hX : Integrable X πs)
    (horth : ∀ h : Rd d × Y → ℝ, Measurable h → (∀ z, |h z| ≤ 1 / 2) →
      (∀ A : Set Y, MeasurableSet A → ∫ z in Prod.snd ⁻¹' A, h z ∂πs = 0) →
      ∫ z, X z * h z ∂πs = 0) :
    ∃ c : Y → ℝ, Measurable c ∧ X =ᵐ[πs] fun z => c z.2 := by
  let mY : MeasurableSpace (Rd d × Y) := MeasurableSpace.comap Prod.snd ‹MeasurableSpace Y›
  have hle : mY ≤ (Prod.instMeasurableSpace : MeasurableSpace (Rd d × Y)) := by
    rintro s ⟨t, ht, rfl⟩
    exact measurable_snd ht
  have hφc := clamp_continuous
  let e : Rd d × Y → ℝ := πs[X|mY]
  have hem : StronglyMeasurable[mY] e := stronglyMeasurable_condExp
  have heint : Integrable e πs := integrable_condExp
  let w : Rd d × Y → ℝ := fun z => max (-(1 / 4 : ℝ)) (min (1 / 4) (X z - e z))
  have hwm : Measurable[Prod.instMeasurableSpace] w := hφc.measurable.comp (hXm.sub (hem.mono hle).measurable)
  have hwb : ∀ z, |w z| ≤ 1 / 4 := fun z => clamp_abs_le _
  have hwint : Integrable w πs := integrable_of_abs_le hwm.aestronglyMeasurable hwb
  let k : Rd d × Y → ℝ := πs[w|mY]
  have hkm : StronglyMeasurable[mY] k := stronglyMeasurable_condExp
  let kk : Rd d × Y → ℝ := fun z => max (-(1 / 4 : ℝ)) (min (1 / 4) (k z))
  have hkkm : StronglyMeasurable[mY] kk := hφc.comp_stronglyMeasurable hkm
  have hkkb : ∀ z, |kk z| ≤ 1 / 4 := fun z => clamp_abs_le _
  have hkkint : Integrable kk πs :=
    integrable_of_abs_le (hkkm.mono hle).aestronglyMeasurable hkkb
  have hkb : ∀ᵐ z ∂πs, |k z| ≤ ((4⁻¹ : NNReal) : ℝ) :=
    ae_bdd_condExp_of_ae_bdd (ae_of_all _ fun z => by
      have := hwb z
      rw [NNReal.coe_inv]; norm_num at this ⊢; exact this)
  have hkk : kk =ᵐ[πs] k := by
    filter_upwards [hkb] with z hz
    have hz' : |k z| ≤ 1 / 4 := by rw [NNReal.coe_inv] at hz; norm_num at hz ⊢; exact hz
    rw [abs_le] at hz'
    show max (-(1 / 4 : ℝ)) (min (1 / 4) (k z)) = k z
    rw [min_eq_right hz'.2, max_eq_right hz'.1]
  let h : Rd d × Y → ℝ := fun z => w z - kk z
  have hhm : Measurable[Prod.instMeasurableSpace] h := hwm.sub (hkkm.mono hle).measurable
  have hhb : ∀ z, |h z| ≤ 1 / 2 := fun z => by
    have h1 := abs_le.mp (hwb z)
    have h2 := abs_le.mp (hkkb z)
    show |w z - kk z| ≤ 1 / 2
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hadm : ∀ A : Set Y, MeasurableSet A → ∫ z in Prod.snd ⁻¹' A, h z ∂πs = 0 := by
    intro A hA
    have hA' : MeasurableSet[mY] (Prod.snd ⁻¹' A) := ⟨A, hA, rfl⟩
    show ∫ z in Prod.snd ⁻¹' A, (w z - kk z) ∂πs = 0
    rw [integral_sub hwint.integrableOn hkkint.integrableOn,
      integral_congr_ae (ae_restrict_of_ae hkk), setIntegral_condExp hle hwint hA', sub_self]
  have h0 := horth h hhm hhb hadm
  have hXw : Integrable (fun z => X z * w z) πs :=
    (integrable_mul_bdd hX hwm.aestronglyMeasurable hwb).congr
      (ae_of_all _ fun z => mul_comm _ _)
  have hXkk' : Integrable (fun z => X z * kk z) πs :=
    (integrable_mul_bdd hX (hkkm.mono hle).aestronglyMeasurable hkkb).congr
      (ae_of_all _ fun z => mul_comm _ _)
  have hew' : Integrable (fun z => e z * w z) πs :=
    (integrable_mul_bdd heint hwm.aestronglyMeasurable hwb).congr
      (ae_of_all _ fun z => mul_comm _ _)
  have hXkk : ∫ z, X z * kk z ∂πs = ∫ z, e z * kk z ∂πs := by
    have hi : Integrable (kk * X) πs :=
      integrable_mul_bdd hX (hkkm.mono hle).aestronglyMeasurable hkkb
    have := condExp_mul_of_stronglyMeasurable_left hkkm hi hX
    calc ∫ z, X z * kk z ∂πs = ∫ z, (kk * X) z ∂πs := by
          congr 1; funext z; simp only [Pi.mul_apply]; ring
      _ = ∫ z, (πs[kk * X|mY]) z ∂πs := (integral_condExp hle).symm
      _ = ∫ z, (kk * e) z ∂πs := integral_congr_ae this
      _ = ∫ z, e z * kk z ∂πs := by
          congr 1; funext z; simp only [Pi.mul_apply]; ring
  have hew : ∫ z, e z * w z ∂πs = ∫ z, e z * kk z ∂πs := by
    have hi : Integrable (e * w) πs := hew'
    have := condExp_mul_of_stronglyMeasurable_left hem hi hwint
    calc ∫ z, e z * w z ∂πs = ∫ z, (e * w) z ∂πs := rfl
      _ = ∫ z, (πs[e * w|mY]) z ∂πs := (integral_condExp hle).symm
      _ = ∫ z, (e * k) z ∂πs := integral_congr_ae this
      _ = ∫ z, e z * kk z ∂πs := by
          refine integral_congr_ae ?_
          filter_upwards [hkk] with z hz
          simp only [Pi.mul_apply, hz]
  have hXh : ∫ z, X z * h z ∂πs = ∫ z, X z * w z ∂πs - ∫ z, X z * kk z ∂πs := by
    rw [← integral_sub hXw hXkk']
    congr 1; funext z
    show X z * (w z - kk z) = _
    ring
  have hpos : ∫ z, (X z - e z) * w z ∂πs = 0 := by
    have hsplit : (fun z => (X z - e z) * w z) = fun z => X z * w z - e z * w z :=
      funext fun z => by ring
    rw [hsplit, integral_sub hXw hew', hew, ← hXkk, ← hXh, h0]
  have hint2 : Integrable (fun z => (X z - e z) * w z) πs :=
    (hXw.sub hew').congr (ae_of_all _ fun z => by simp only [Pi.sub_apply]; ring)
  have hnn : 0 ≤ fun z => (X z - e z) * w z := fun z => mul_clamp_nonneg _
  have hz := (integral_eq_zero_iff_of_nonneg hnn hint2).mp hpos
  have hXe : X =ᵐ[πs] e := by
    filter_upwards [hz] with z hz
    by_contra hne
    exact (mul_clamp_pos (sub_ne_zero.mpr hne)).ne' hz
  obtain ⟨c, hc, hce⟩ := hem.exists_eq_measurable_comp
  refine ⟨c, hc.measurable, ?_⟩
  filter_upwards [hXe] with z hz
  rw [hz, hce]; rfl

lemma xi_ae_comp_snd {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ}
    {F : Measure (Rd d × Y) → ℝ} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ}
    (hA : Assumption21 m p F δF) {η : ℝ} (hη : 0 < η) {πs : Measure (Rd d × Y)}
    (hmin : IsMinimizer m p F η πs) :
    ∃ c : Y → ℝ, Measurable c ∧
      (fun z => δF πs z.1 z.2 + η * logDens m πs z) =ᵐ[πs] fun z => c z.2 := by
  have hπP := hmin.1
  haveI := hπP.1
  have hp := hA.one_le_p
  obtain ⟨hac, hint⟩ := minimizer_ac hp hη hmin
  obtain ⟨C, y₀, hC⟩ := hA.growth
  have hδm : Measurable (fun z : Rd d × Y => δF πs z.1 z.2) := hA.linDeriv.1 πs hπP
  have hδint : Integrable (fun z : Rd d × Y => δF πs z.1 z.2) πs :=
    integrable_of_growth hp hπP hδm C ((0 : Rd d), y₀) fun z => hC πs hπP z.1 z.2
  have hLm : Measurable (logDens m πs) := (Measure.measurable_rnDeriv _ _).ennreal_toReal.log
  refine ae_eq_comp_snd_of_orth (hδm.add (measurable_const.mul hLm))
    (hδint.add (hint.const_mul η)) ?_
  intro h hm hb hadm
  have e0 := first_variation_eq_zero hA hη hmin hm hb hadm
  have i1 : Integrable (fun z => δF πs z.1 z.2 * h z) πs :=
    (integrable_mul_bdd (C := 1 / 2) hδint hm.aestronglyMeasurable hb).congr
      (ae_of_all _ fun z => mul_comm _ _)
  have i2 : Integrable (fun z => h z * logDens m πs z) πs :=
    integrable_mul_bdd (C := 1 / 2) hint hm.aestronglyMeasurable hb
  rw [← integral_const_mul, ← integral_add i1 (i2.const_mul η)] at e0
  rw [← e0]; congr 1; funext z; ring

end L6E

/-! ## L8 (step E): first-order condition from `Ξ = c(y)` and positivity -/

section L8

lemma foc_of_xi_const {m : Measure Y} {p : ℝ}
    {F : Measure (Rd d × Y) → ℝ} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ}
    (hA : Assumption21 m p F δF) {η : ℝ} (hη : 0 < η) {πs : Measure (Rd d × Y)}
    (hπP : πs ∈ Pi (d := d) m p) {ρ : Rd d × Y → ℝ}
    (hπ : πs = (volume.prod m).withDensity (fun z => ENNReal.ofReal (ρ z)))
    (hpos : ∀ᵐ z ∂(volume.prod m), 0 < ρ z) {c : Y → ℝ} (hc : Measurable c)
    (hxi : ∀ᵐ z ∂(volume.prod m), δF πs z.1 z.2 + η * Real.log (ρ z) = c z.2) :
    FirstOrderCondition m δF η πs := by
  have hδm : Measurable (fun z : Rd d × Y => δF πs z.1 z.2) := hA.linDeriv.1 πs hπP
  refine ⟨fun z => Real.exp ((c z.2 - δF πs z.1 z.2) / η), ?_, ?_, ?_⟩
  · exact Real.measurable_exp.comp (((hc.comp measurable_snd).sub hδm).div_const η)
  · refine hπ.trans (withDensity_congr_ae ?_)
    filter_upwards [hpos, hxi] with z hz1 hz2
    congr 1
    rw [← Real.exp_log hz1]
    congr 1
    field_simp
    linarith
  · refine ae_of_all _ fun y x => ?_
    have hfun : (fun x' => Real.log (Real.exp ((c (x', y).2 - δF πs (x', y).1 (x', y).2) / η)))
        = fun x' => η⁻¹ * (c y - δF πs x' y) := by
      funext x'
      rw [Real.log_exp, div_eq_inv_mul]
    have hd : Differentiable ℝ (fun x' => δF πs x' y) :=
      (hA.contDiff πs hπP y).differentiable one_ne_zero
    have hd2 : DifferentiableAt ℝ (fun x' => c y - δF πs x' y) x :=
      (differentiableAt_const _).sub (hd x)
    refine ⟨Real.exp_pos _, ?_, ?_⟩
    · rw [hfun]; exact hd2.const_mul _
    · rw [hfun]
      unfold gradient
      rw [fderiv_const_mul hd2, fderiv_const_sub, map_smul, map_neg, smul_smul,
        mul_inv_cancel₀ hη.ne', one_smul, add_neg_cancel]

end L8

/-! ## L6F (step D): the minimizer's density is positive a.e.; assembly of part 1 -/

section L6F
variable [SecondCountableTopology Y] [BorelSpace Y]

lemma integrable_wd_iff {μ : Measure (Rd d × Y)} {u : Rd d × Y → ℝ} (hu : Measurable u)
    (hu0 : ∀ z, 0 ≤ u z) {f : Rd d × Y → ℝ} :
    Integrable f (μ.withDensity (fun z => ENNReal.ofReal (u z))) ↔
      Integrable (fun z => u z * f z) μ := by
  rw [integrable_withDensity_iff_integrable_smul' hu.ennreal_ofReal
    (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
  exact integrable_congr (ae_of_all _ fun z => by
    simp only [ENNReal.toReal_ofReal (hu0 z), smul_eq_mul])

lemma integral_wd {μ : Measure (Rd d × Y)} {u : Rd d × Y → ℝ} (hu : Measurable u)
    (hu0 : ∀ z, 0 ≤ u z) (f : Rd d × Y → ℝ) :
    ∫ z, f z ∂(μ.withDensity (fun z => ENNReal.ofReal (u z))) = ∫ z, u z * f z ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hu.ennreal_ofReal
    (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (ae_of_all _ fun z => by
    simp only [ENNReal.toReal_ofReal (hu0 z), smul_eq_mul])

lemma relEnt_wd_eq {m : Measure Y} [IsProbabilityMeasure m] {u : Rd d × Y → ℝ}
    (hu : Measurable u) (hu0 : ∀ z, 0 ≤ u z)
    (hi : Integrable (fun z => u z * Real.log (u z)) (volume.prod m)) :
    relEnt m ((volume.prod m).withDensity (fun z => ENNReal.ofReal (u z))) =
      ((∫ z, u z * Real.log (u z) ∂(volume.prod m) : ℝ) : EReal) := by
  have hac : (volume.prod m).withDensity (fun z => ENNReal.ofReal (u z)) ≪ volume.prod m :=
    withDensity_absolutelyContinuous _ _
  have hae : logDens m ((volume.prod m).withDensity (fun z => ENNReal.ofReal (u z)))
      =ᵐ[(volume.prod m).withDensity (fun z => ENNReal.ofReal (u z))]
        fun z => Real.log (u z) := by
    filter_upwards [hac.ae_le (logDens_ae_eq (m := m) hu rfl)] with z hz
    rw [hz, max_eq_left (hu0 z)]
  have hint : Integrable (logDens m ((volume.prod m).withDensity (fun z => ENNReal.ofReal (u z))))
      ((volume.prod m).withDensity (fun z => ENNReal.ofReal (u z))) := by
    refine (integrable_congr hae).2 ?_
    exact (integrable_wd_iff hu hu0).2 hi
  unfold relEnt
  rw [if_pos ⟨hac, hint⟩, integral_congr_ae hae, integral_wd hu hu0]

lemma mul_log_mix_le {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((1 - t) * a + t * b) * Real.log ((1 - t) * a + t * b) ≤
      (1 - t) * (a * Real.log a) + t * (b * Real.log b) +
        (if a = 0 then t * Real.log t * b else 0) := by
  rcases ha.eq_or_lt with h | h
  · subst h
    rw [if_pos rfl]
    simp only [mul_zero, zero_add, zero_mul]
    rw [Real.log_mul ht0.ne' hb.ne']
    apply le_of_eq
    ring
  · rw [if_neg h.ne', add_zero]
    have := Real.convexOn_mul_log.2 (Set.mem_Ici.2 h.le) (Set.mem_Ici.2 hb.le)
      (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    simpa only [smul_eq_mul] using this

lemma rnDeriv_pos {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ}
    {F : Measure (Rd d × Y) → ℝ} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ}
    (hA : Assumption21 m p F δF) {η : ℝ} (hη : 0 < η) {πs : Measure (Rd d × Y)}
    (hmin : IsMinimizer m p F η πs) :
    ∀ᵐ z ∂(volume.prod m), 0 < (πs.rnDeriv (volume.prod m) z).toReal := by
  have hπP := hmin.1
  haveI := hπP.1
  have hp := hA.one_le_p
  obtain ⟨hac, hint⟩ := minimizer_ac hp hη hmin
  have hπ0 := eq_withDensity_rnDeriv hac
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Rd d × Y → ℝ,
      ρ = fun z => (πs.rnDeriv (volume.prod m) z).toReal := ⟨_, rfl⟩
  have hρm : Measurable ρ := by
    rw [hρdef]; exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hρ0 : ∀ z, 0 ≤ ρ z := fun z => by rw [hρdef]; exact ENNReal.toReal_nonneg
  have hπ : πs = (volume.prod m).withDensity (fun z => ENNReal.ofReal (ρ z)) := by
    rw [hρdef]; exact hπ0
  obtain ⟨g, hgm, hgpos, hν0P, hgint, C, z1, hgC⟩ := ref_measure hp hπP
  haveI : IsProbabilityMeasure ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))) :=
    hν0P.1
  have hg1m : Measurable (fun z : Rd d × Y => g z.1) := hgm.comp measurable_fst
  have hg10 : ∀ z : Rd d × Y, 0 ≤ g z.1 := fun z => (hgpos z.1).le
  -- integrability facts with respect to `μ0 = Leb × m`
  have hHs_int : Integrable (fun z => ρ z * Real.log (ρ z)) (volume.prod m) := by
    have hl : logDens m πs = fun z => Real.log (ρ z) := by rw [hρdef]; rfl
    have h1 : Integrable (fun z => Real.log (ρ z)) πs := by rw [← hl]; exact hint
    rw [hπ] at h1
    exact (integrable_wd_iff hρm hρ0).1 h1
  have hgρ_int : Integrable (fun z => ρ z * Real.log (g z.1)) (volume.prod m) := by
    have h1 : Integrable (fun z : Rd d × Y => Real.log (g z.1)) πs :=
      integrable_of_growth hp hπP (Real.measurable_log.comp hg1m) C z1 hgC
    rw [hπ] at h1
    exact (integrable_wd_iff hρm hρ0).1 h1
  have hH0_int : Integrable (fun z => g z.1 * Real.log (g z.1)) (volume.prod m) :=
    (integrable_wd_iff (u := fun z => g z.1) hg1m hg10).1 hgint
  have hρint : Integrable ρ (volume.prod m) := by
    have h1 : Integrable (fun _ => (1 : ℝ)) πs := integrable_const _
    rw [hπ] at h1
    simpa using (integrable_wd_iff hρm hρ0).1 h1
  have hgint1 : Integrable (fun z : Rd d × Y => g z.1) (volume.prod m) := by
    have h1 : Integrable (fun _ => (1 : ℝ))
        ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))) := integrable_const _
    simpa using (integrable_wd_iff (u := fun z => g z.1) hg1m hg10).1 h1
  set A : Set (Rd d × Y) := {z | ρ z = 0} with hAdef
  have hAm : MeasurableSet A := hρm (measurableSet_singleton 0)
  have hIA : Integrable (A.indicator (fun z => g z.1)) (volume.prod m) := hgint1.indicator hAm
  have hInn : 0 ≤ A.indicator (fun z : Rd d × Y => g z.1) :=
    fun z => Set.indicator_nonneg (fun z _ => hg10 z) z
  set a : ℝ := ∫ z, A.indicator (fun z => g z.1) z ∂(volume.prod m) with hadef
  have ha0 : 0 ≤ a := integral_nonneg hInn
  set Hs : ℝ := ∫ z, ρ z * Real.log (ρ z) ∂(volume.prod m) with hHs
  set H0 : ℝ := ∫ z, g z.1 * Real.log (g z.1) ∂(volume.prod m) with hH0
  have hrelS : relEnt m πs = (Hs : EReal) := by
    rw [hπ]; exact relEnt_wd_eq hρm hρ0 hHs_int
  have ha : a = 0 := by
    by_contra hne
    have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hne)
    have key : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        0 ≤ (F (mix t πs ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))))
          - F πs) / t + η * (H0 - Hs) + η * a * Real.log t := by
      intro t ht
      set u : Rd d × Y → ℝ := fun z => (1 - t) * ρ z + t * g z.1 with hu
      have hum : Measurable u := (hρm.const_mul _).add (hg1m.const_mul _)
      have hu0 : ∀ z, 0 ≤ u z := fun z =>
        add_nonneg (mul_nonneg (by linarith [ht.2]) (hρ0 z)) (mul_nonneg ht.1.le (hg10 z))
      have hmix : mix t πs ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))) =
          (volume.prod m).withDensity (fun z => ENNReal.ofReal (u z)) := by
        rw [hπ]
        unfold mix
        rw [← withDensity_smul _ hρm.ennreal_ofReal, ← withDensity_smul _ hg1m.ennreal_ofReal,
          ← withDensity_add_left (hρm.ennreal_ofReal.const_smul _)]
        congr 1
        funext z
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu]
        rw [ENNReal.ofReal_add (mul_nonneg (by linarith [ht.2]) (hρ0 z))
            (mul_nonneg ht.1.le (hg10 z)),
          ENNReal.ofReal_mul (by linarith [ht.2]), ENNReal.ofReal_mul ht.1.le]
      have hPt := mix_mem_Pi hp hπP hν0P (t := t) ⟨ht.1.le, ht.2.le⟩
      have hle := hmin.2 _ hPt
      set B : Rd d × Y → ℝ := fun z => (1 - t) * (ρ z * Real.log (ρ z)) +
        t * (g z.1 * Real.log (g z.1)) + t * Real.log t * A.indicator (fun z => g z.1) z with hB
      have hB1 : Integrable (fun z => (1 - t) * (ρ z * Real.log (ρ z))) (volume.prod m) :=
        hHs_int.const_mul _
      have hB2 : Integrable (fun z => t * (g z.1 * Real.log (g z.1))) (volume.prod m) :=
        hH0_int.const_mul _
      have hB3 : Integrable (fun z => t * Real.log t * A.indicator (fun z => g z.1) z)
          (volume.prod m) := hIA.const_mul _
      have hBint : Integrable B (volume.prod m) := (hB1.add hB2).add hB3
      have hpt : ∀ z, u z * Real.log (u z) ≤ B z := by
        intro z
        have h := mul_log_mix_le (hρ0 z) (hgpos z.1) ht.1 ht.2.le
        by_cases hz : ρ z = 0
        · rw [if_pos hz] at h
          simp only [hB, hu, Set.indicator_of_mem (show z ∈ A from hz)]
          linarith
        · rw [if_neg hz] at h
          simp only [hB, hu, Set.indicator_of_notMem (show z ∉ A from hz)]
          linarith
      set L : Rd d × Y → ℝ := fun z => Real.log t * u z + (1 - t) * (ρ z * Real.log (g z.1)) +
        t * (g z.1 * Real.log (g z.1)) with hL
      have hLint : Integrable L (volume.prod m) :=
        ((((hρint.const_mul (1 - t)).add (hgint1.const_mul t)).const_mul (Real.log t)).add
          (hgρ_int.const_mul _)).add (hH0_int.const_mul _)
      have hlow : ∀ z, L z ≤ u z * Real.log (u z) := by
        intro z
        have htg : 0 < t * g z.1 := mul_pos ht.1 (hgpos z.1)
        have hle' : t * g z.1 ≤ u z := by
          simp only [hu]; nlinarith [hρ0 z, ht.2]
        have h1 : Real.log (t * g z.1) ≤ Real.log (u z) := Real.log_le_log htg hle'
        rw [Real.log_mul ht.1.ne' (hgpos z.1).ne'] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 (hu0 z)
        simp only [hL, hu] at h2 ⊢
        linarith
      have hlogu_int : Integrable (fun z => u z * Real.log (u z)) (volume.prod m) :=
        integrable_of_le_of_le
          ((hum.mul (Real.measurable_log.comp hum)).aestronglyMeasurable)
          (ae_of_all _ hlow) (ae_of_all _ hpt) hLint hBint
      have hHt : relEnt m (mix t πs ((volume.prod m).withDensity
          (fun z => ENNReal.ofReal (g z.1)))) =
          ((∫ z, u z * Real.log (u z) ∂(volume.prod m) : ℝ) : EReal) := by
        rw [hmix]; exact relEnt_wd_eq hum hu0 hlogu_int
      have hIt : ∫ z, u z * Real.log (u z) ∂(volume.prod m) ≤
          (1 - t) * Hs + t * H0 + t * Real.log t * a := by
        calc ∫ z, u z * Real.log (u z) ∂(volume.prod m) ≤ ∫ z, B z ∂(volume.prod m) :=
              integral_mono hlogu_int hBint hpt
          _ = (1 - t) * Hs + t * H0 + t * Real.log t * a := by
              have hB12 : Integrable (fun z => (1 - t) * (ρ z * Real.log (ρ z)) +
                  t * (g z.1 * Real.log (g z.1))) (volume.prod m) := hB1.add hB2
              simp only [hB]
              rw [integral_add hB12 hB3, integral_add hB1 hB2,
                integral_const_mul, integral_const_mul, integral_const_mul]
      unfold V at hle
      rw [hrelS, hHt, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at hle
      have h3 := mul_le_mul_of_nonneg_left hIt hη.le
      have hnum : 0 ≤ (F (mix t πs ((volume.prod m).withDensity
          (fun z => ENNReal.ofReal (g z.1)))) - F πs) + t * (η * (H0 - Hs) + η * a * Real.log t) := by
        linarith
      have hX : (F (mix t πs ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))))
          - F πs) / t + η * (H0 - Hs) + η * a * Real.log t =
          ((F (mix t πs ((volume.prod m).withDensity (fun z => ENNReal.ofReal (g z.1))))
          - F πs) + t * (η * (H0 - Hs) + η * a * Real.log t)) / t := by
        have := ht.1.ne'
        first
          | (field_simp; done)
          | (field_simp; ring)
      rw [hX]
      exact div_nonneg hnum ht.1.le
    have hlim1 := tendsto_slope_F hA hπP hν0P
    have hlim2 : Tendsto (fun s : ℝ => η * a * Real.log s) (𝓝[>] 0) atBot :=
      Real.tendsto_log_nhdsGT_zero.const_mul_atBot (mul_pos hη hapos)
    have hlim := (hlim1.add (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => η * (H0 - Hs)) (𝓝[>] 0) (𝓝 (η * (H0 - Hs))))).add_atBot hlim2
    have hev1 := hlim.eventually (eventually_lt_atBot 0)
    have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
    obtain ⟨s, hs1, hs2⟩ := (hev1.and hev2).exists
    have := key s hs2
    try simp only at hs1
    linarith
  have hAe : A.indicator (fun z => g z.1) =ᵐ[volume.prod m] 0 :=
    (integral_eq_zero_iff_of_nonneg hInn hIA).1 ha
  filter_upwards [hAe] with z hz
  have h1 : A.indicator (fun z => g z.1) z = 0 := hz
  by_cases h0 : ρ z = 0
  · rw [Set.indicator_of_mem (show z ∈ A from h0)] at h1
    exact absurd h1 (hgpos z.1).ne'
  · have := lt_of_le_of_ne (hρ0 z) (Ne.symm h0)
    rw [hρdef] at this
    exact this

theorem part1 {m : Measure Y} [IsProbabilityMeasure m] {p : ℝ}
    {F : Measure (Rd d × Y) → ℝ} {δF : Measure (Rd d × Y) → Rd d → Y → ℝ}
    (hA : Assumption21 m p F δF) {η : ℝ} (hη : 0 < η) {πs : Measure (Rd d × Y)}
    (hmin : IsMinimizer m p F η πs) : FirstOrderCondition m δF η πs := by
  have hπP := hmin.1
  haveI := hπP.1
  obtain ⟨hac, -⟩ := minimizer_ac hA.one_le_p hη hmin
  have hπ := eq_withDensity_rnDeriv hac
  have hpos := rnDeriv_pos hA hη hmin
  obtain ⟨c, hc, hxi⟩ := xi_ae_comp_snd hA hη hmin
  have hμπ : volume.prod m ≪ πs := by
    conv_rhs => rw [hπ]
    refine withDensity_absolutelyContinuous'
      (Measure.measurable_rnDeriv _ _).ennreal_toReal.ennreal_ofReal.aemeasurable ?_
    filter_upwards [hpos] with z hz
    exact (ENNReal.ofReal_pos.2 hz).ne'
  have hxi' : ∀ᵐ z ∂(volume.prod m), δF πs z.1 z.2 +
      η * Real.log ((πs.rnDeriv (volume.prod m) z).toReal) = c z.2 := hμπ.ae_le hxi
  exact foc_of_xi_const hA hη hπP hπ hpos hc hxi'

end L6F

end GameRandEnv.FirstOrder.Aux

open MeasureTheory Filter Topology GameRandEnv.FirstOrder in
theorem solution {d : ℕ} {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [IsProbabilityMeasure m] (p : ℝ)
    (F : Measure (Rd d × Y) → ℝ) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ)
    (hA : Assumption21 m p F δF) (η : ℝ) (hη : 0 < η)
    (πs : Measure (Rd d × Y)) :
    (IsMinimizer m p F η πs → FirstOrderCondition m δF η πs) ∧
    (ConvexOnPi m p F → πs ∈ Pi m p → FirstOrderCondition m δF η πs →
      IsMinimizer m p F η πs) := by
  exact ⟨fun h => GameRandEnv.FirstOrder.Aux.part1 hA hη h,
    fun hc hP hf => GameRandEnv.FirstOrder.Aux.part2 hA hη hc hP hf⟩
