-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.market_profit_regular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:50.198687+00:00
-- url     : https://prove2.me/submissions/c2cb5dd0-ee83-4ca4-bee5-8674768a644d

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Set

namespace CohenPriceFairness.LocalWelfare.Sol_market_profit_regular
open CohenPriceFairness.LocalWelfare

section L1measure
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma l1_D_le_one (p : ℝ) : (μ (Ici p)).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := μ) (s := Ici p))

lemma l1_D_anti {p q : ℝ} (h : p ≤ q) : (μ (Ici q)).toReal ≤ (μ (Ici p)).toReal :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ici_subset_Ici.mpr h))

lemma l1_D_usc (p η : ℝ) (hη : 0 < η) :
    ∀ᶠ q in 𝓝 p, (μ (Ici q)).toReal < (μ (Ici p)).toReal + η := by
  have ht := tendsto_measure_biInter_gt (μ := μ) (s := fun r : ℝ => Ici (p - r)) (a := 0)
    (fun r _ => measurableSet_Ici.nullMeasurableSet)
    (fun i j _ hij => Ici_subset_Ici.mpr (by linarith)) ⟨1, one_pos, measure_ne_top _ _⟩
  have hI : (⋂ r > (0:ℝ), Ici (p - r)) = Ici p := by
    ext x; simp only [mem_iInter, mem_Ici]
    constructor
    · intro h
      by_contra hx; push Not at hx
      have := h ((p - x) / 2) (by linarith); linarith
    · intro hx r hr; linarith
  rw [hI] at ht
  have ht' := (ENNReal.tendsto_toReal (measure_ne_top μ (Ici p))).comp ht
  have hev : ∀ᶠ r in 𝓝[>] (0:ℝ), (μ (Ici (p - r))).toReal < (μ (Ici p)).toReal + η :=
    ht'.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r, hr, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0' : 0 < r := hr0
  filter_upwards [Ioi_mem_nhds (show p - r < p by linarith)] with q hq
  exact lt_of_le_of_lt (l1_D_anti (le_of_lt hq)) hr

lemma l1_tail (hint : Integrable (fun v : ℝ => v) μ) :
    Tendsto (fun p : ℝ => p * (μ (Ici p)).toReal) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun p v => (Ici p).indicator (fun _ => p) v) (f := fun _ => (0:ℝ)) (fun v => |v|)
    (Eventually.of_forall fun p =>
      (aestronglyMeasurable_const.indicator measurableSet_Ici)) ?_ hint.abs ?_
  · simp only [integral_zero] at h
    refine h.congr' ?_
    filter_upwards with p
    rw [integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_comm]
    rfl
  · filter_upwards [eventually_ge_atTop 0] with p hp
    refine Eventually.of_forall fun v => ?_
    by_cases hv : p ≤ v
    · simp [indicator, hv, abs_of_nonneg hp, abs_of_nonneg (hp.trans hv)]
    · simp [indicator, hv]
  · refine Eventually.of_forall fun v => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop v] with p hp
    simp [indicator, not_le.mpr hp]

end L1measure

lemma l1_demand_nonneg (m : Market) (i : Fin 2) (p : ℝ) : 0 ≤ demand m i p :=
  ENNReal.toReal_nonneg

lemma l1_pos (m : Market) (hm : m.Admissible) (b : Prices)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i) (i : Fin 2) :
    0 < profit m i (b i) ∧ m.cost < b i ∧ 0 < demand m i (b i) := by
  have hc := hm.1
  have hd := (hm.2 i).1
  have hD := l1_demand_nonneg m i
  have hR : 0 < profit m i (b i) := by
    by_contra h; push Not at h
    have hmx := le_max_left m.cost (b i)
    have hmx2 := le_max_right m.cost (b i)
    have hp0 : 0 ≤ max m.cost (b i) + 1 := by linarith
    have hRp : 0 ≤ profit m i (max m.cost (b i) + 1) := by
      unfold profit
      have : 0 ≤ max m.cost (b i) + 1 - m.cost := by linarith
      have := hD (max m.cost (b i) + 1); positivity
    have := huniq i _ hp0 (h.trans hRp)
    linarith
  refine ⟨hR, ?_⟩
  have h1 : 0 < (b i - m.cost) * demand m i (b i) := by
    have : profit m i (b i) = m.population i * ((b i - m.cost) * demand m i (b i)) := by
      unfold profit; ring
    rw [this] at hR
    exact (mul_pos_iff_of_pos_left hd).mp hR
  rcases mul_pos_iff.mp h1 with h | h
  · exact ⟨by linarith [h.1], h.2⟩
  · exact absurd h.2 (not_lt.mpr (hD _))

lemma l1_R_bound (m : Market) (hm : m.Admissible) (i : Fin 2) (p q : ℝ) (hp : m.cost ≤ p) :
    profit m i q ≤ profit m i p + m.population i * |q - p| +
      m.population i * (p - m.cost) * (demand m i q - demand m i p) := by
  have := (hm.2 i).2.1
  have hd := (hm.2 i).1
  have hD0 := l1_demand_nonneg m i q
  have hD1 : demand m i q ≤ 1 := l1_D_le_one q
  have h1 : (q - p) * demand m i q ≤ |q - p| := by
    calc (q - p) * demand m i q ≤ |q - p| * demand m i q :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hD0
      _ ≤ |q - p| * 1 := mul_le_mul_of_nonneg_left hD1 (abs_nonneg _)
      _ = |q - p| := mul_one _
  have : profit m i q - profit m i p = m.population i * ((q - p) * demand m i q) +
      m.population i * (p - m.cost) * (demand m i q - demand m i p) := by
    unfold profit; ring
  have h2 := mul_le_mul_of_nonneg_left h1 hd.le
  linarith

lemma l1_R_usc (m : Market) (hm : m.Admissible) (i : Fin 2) (p : ℝ) (hp : m.cost ≤ p)
    (y : ℝ) (hy : profit m i p < y) : ∀ᶠ q in 𝓝 p, profit m i q < y := by
  have := (hm.2 i).2.1
  have hd := (hm.2 i).1
  set η := (y - profit m i p) / (2 * m.population i * (1 + (p - m.cost))) with hη
  have hpos : 0 < 2 * m.population i * (1 + (p - m.cost)) := by
    have : 0 < 1 + (p - m.cost) := by linarith
    positivity
  have hη0 : 0 < η := div_pos (by linarith) hpos
  have hηe : m.population i * η * (1 + (p - m.cost)) = (y - profit m i p) / 2 := by
    have : 1 + (p - m.cost) ≠ 0 := by linarith
    rw [hη]; field_simp
  filter_upwards [l1_D_usc (μ := m.law i) p η hη0, Metric.ball_mem_nhds p hη0] with q hq1 hq2
  have hq2' : |q - p| < η := hq2
  have hb := l1_R_bound m hm i p q hp
  have e1 : m.population i * |q - p| ≤ m.population i * η :=
    mul_le_mul_of_nonneg_left hq2'.le hd.le
  have e2 : m.population i * (p - m.cost) * (demand m i q - demand m i p) ≤
      m.population i * (p - m.cost) * η := by
    apply mul_le_mul_of_nonneg_left _ (by have := sub_nonneg.mpr hp; positivity)
    have : demand m i q < demand m i p + η := hq1
    linarith
  nlinarith

lemma l1_loc_i (m : Market) (hm : m.Admissible) (b : Prices) (hb : BaselineOptimal m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i) (i : Fin 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p → |p - b i| < ε := by
  have := (hm.2 i).2.1
  have hd := (hm.2 i).1
  have hc := hm.1
  obtain ⟨hR, hcb, hDb⟩ := l1_pos m hm b huniq i
  set Rb := profit m i (b i)
  -- tail
  have ht := (l1_tail (μ := m.law i) (hm.2 i).2.2.2).const_mul (m.population i)
  rw [mul_zero] at ht
  obtain ⟨M, hM⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hR)))
  have htail : ∀ p, 0 ≤ p → M ≤ p → profit m i p < Rb / 2 := by
    intro p hp hMp
    have := hM p hMp
    have hD0 := l1_demand_nonneg m i p
    have : profit m i p ≤ m.population i * (p * demand m i p) := by
      unfold profit
      have : (p - m.cost) * demand m i p ≤ p * demand m i p :=
        mul_le_mul_of_nonneg_right (by linarith) hD0
      have := mul_le_mul_of_nonneg_left this hd.le
      linarith
    simp only [demand] at *
    linarith
  set K := Icc m.cost M ∩ {p | ε ≤ |p - b i|} with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hgapK : ∃ δ' > 0, ∀ p ∈ K, profit m i p + δ' ≤ Rb := by
    rcases K.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · have husc : UpperSemicontinuousOn (profit m i) K := by
        intro p hp y hy
        exact (l1_R_usc m hm i p hp.1.1 y hy).filter_mono nhdsWithin_le_nhds
      obtain ⟨p0, hp0, hmax⟩ := husc.exists_isMaxOn h hKc
      have hle := (hb i).2 p0 (hc.trans hp0.1.1)
      have hne : profit m i p0 ≠ Rb := by
        intro heq
        have := huniq i p0 (hc.trans hp0.1.1) heq.ge
        have h2 : ε ≤ |p0 - b i| := hp0.2
        rw [this, sub_self, abs_zero] at h2
        linarith
      refine ⟨Rb - profit m i p0, by
        have := lt_of_le_of_ne hle hne; linarith, fun p hp => ?_⟩
      have := hmax hp
      simp only [mem_ofPred_eq] at this
      linarith
  obtain ⟨δ', hδ', hK'⟩ := hgapK
  refine ⟨min (Rb / 2) (δ' / 2), lt_min (half_pos hR) (half_pos hδ'), fun p hp hRp => ?_⟩
  have hm1 := min_le_left (Rb / 2) (δ' / 2)
  have hm2 := min_le_right (Rb / 2) (δ' / 2)
  have hpc : m.cost ≤ p := by
    by_contra h; push Not at h
    have : profit m i p ≤ 0 := by
      unfold profit
      have : m.population i * (p - m.cost) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hd.le (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg this (l1_demand_nonneg m i p)
    linarith
  have hpM : p ≤ M := by
    by_contra h; push Not at h
    have := htail p hp h.le
    linarith
  by_contra h; push Not at h
  have := hK' p ⟨⟨hpc, hpM⟩, h⟩
  linarith

lemma l1_loc (m : Market) (hm : m.Admissible) (b : Prices) (hb : BaselineOptimal m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i) :
    ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε := by
  intro ε hε
  obtain ⟨δ0, h0, H0⟩ := l1_loc_i m hm b hb huniq 0 ε hε
  obtain ⟨δ1, h1, H1⟩ := l1_loc_i m hm b hb huniq 1 ε hε
  refine ⟨min δ0 δ1, lt_min h0 h1, fun i p hp hRp => ?_⟩
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · exact H0 p hp (le_trans (by linarith [min_le_left δ0 δ1]) hRp)
  · exact H1 p hp (le_trans (by linarith [min_le_right δ0 δ1]) hRp)

/-- Second-order Peano expansion at a critical point. -/
lemma l1_taylor (f : ℝ → ℝ) (x : ℝ) (hf : TwiceDifferentiableAt f x) (h0 : deriv f x = 0) :
    (fun h => f (x + h) - f x - deriv (deriv f) x / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2) := by
  obtain ⟨hev, hd2⟩ := hf
  set a := deriv (deriv f) x
  have ho := hd2.hasDerivAt.isLittleO
  rw [Asymptotics.isLittleO_iff] at ho ⊢
  intro ε hε
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp ((ho hε).and hev)
  rw [Metric.eventually_nhds_iff]
  refine ⟨ρ, hρ, fun h hh => ?_⟩
  have hh' : |h| < ρ := by simpa using hh
  have hsub : ∀ t ∈ Icc (-|h|) |h|, dist (x + t) x < ρ := by
    intro t ht
    rw [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs]
    exact lt_of_le_of_lt (abs_le.mpr ht) hh'
  have key : ∀ t ∈ Icc (-|h|) |h|, HasDerivWithinAt (fun t => f (x + t) - f x - a / 2 * t ^ 2)
      (deriv f (x + t) - a * t) (Icc (-|h|) |h|) t := by
    intro t ht
    have hdf := ((hball (hsub t ht)).2).hasDerivAt
    have h1 := hdf.comp_const_add x t
    have h2 : HasDerivAt (fun t : ℝ => a / 2 * t ^ 2) (a / 2 * (2 * t)) t := by
      have := (hasDerivAt_pow 2 t).const_mul (a / 2)
      simpa using this
    have h3 := (h1.sub_const (f x)).sub h2
    exact h3.hasDerivWithinAt.congr_deriv (by ring)
  have bound : ∀ t ∈ Icc (-|h|) |h|, ‖deriv f (x + t) - a * t‖ ≤ ε * |h| := by
    intro t ht
    have := (hball (hsub t ht)).1
    rw [h0] at this
    simp only [add_sub_cancel_left, sub_zero, smul_eq_mul, Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs, mul_comm a t]
    exact this.trans (mul_le_mul_of_nonneg_left (abs_le.mpr ht) hε.le)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le key bound (convex_Icc _ _)
    (x := 0) (y := h) ⟨by simp, by simp⟩ ⟨neg_abs_le h, le_abs_self h⟩
  simp only [add_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, sub_zero, Real.norm_eq_abs] at hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  calc _ ≤ ε * |h| * |h| := hm
    _ = ε * |h| ^ 2 := by ring

/-- The surplus has `-demand` as a subgradient. -/
lemma l1_surplus_sub (m : Market) (hm : m.Admissible) (i : Fin 2) (b p : ℝ) :
    surplus m i b - (p - b) * demand m i b ≤ surplus m i p := by
  have := (hm.2 i).2.1
  have hint := (hm.2 i).2.2.2
  have i1 : Integrable (fun v => max (v - p) 0) (m.law i) := (hint.sub (integrable_const p)).pos_part
  have i2 : Integrable (fun v => max (v - b) 0) (m.law i) := (hint.sub (integrable_const b)).pos_part
  have i3 : Integrable ((Ici b).indicator (fun _ => -(p - b))) (m.law i) :=
    (integrable_const _).indicator measurableSet_Ici
  have hmono : ∫ v, (Ici b).indicator (fun _ => -(p - b)) v ∂m.law i ≤
      ∫ v, (max (v - p) 0 - max (v - b) 0) ∂m.law i := by
    apply integral_mono i3 (i1.sub i2)
    intro v
    simp only [Pi.sub_apply]
    by_cases hv : b ≤ v
    · simp only [indicator, mem_Ici, hv, if_true]
      rw [max_eq_left (show 0 ≤ v - b by linarith)]
      have := le_max_left (v - p) 0
      linarith
    · simp only [indicator, mem_Ici, hv, if_false]
      rw [max_eq_right (show v - b ≤ 0 by linarith)]
      have := le_max_right (v - p) 0
      linarith
  rw [integral_indicator_const _ measurableSet_Ici, integral_sub i1 i2, smul_eq_mul] at hmono
  unfold surplus demand
  have : (m.law i).real (Ici b) = (m.law i (Ici b)).toReal := rfl
  rw [this] at hmono
  linarith

lemma l1_surplus_deriv (m : Market) (hm : m.Admissible) (i : Fin 2) (x : ℝ)
    (hS : DifferentiableAt ℝ (surplus m i) x) :
    HasDerivAt (surplus m i) (-demand m i x) x := by
  have hd := hS.hasDerivAt
  have hg : HasDerivAt (fun p => surplus m i p + p * demand m i x)
      (deriv (surplus m i) x + 1 * demand m i x) x :=
    hd.add ((hasDerivAt_id x).mul_const _)
  have hmin : IsLocalMin (fun p => surplus m i p + p * demand m i x) x := by
    refine Eventually.of_forall fun p => ?_
    have := l1_surplus_sub m hm i x p
    show surplus m i x + x * demand m i x ≤ surplus m i p + p * demand m i x
    nlinarith
  have := hmin.hasDerivAt_eq_zero hg
  have : deriv (surplus m i) x = -demand m i x := by linarith
  rw [← this]; exact hd
lemma l1_eta (x : ℝ) {P : ℝ → Prop} (h : ∀ᶠ y in 𝓝 x, P y) :
    ∃ η > 0, ∀ y ∈ Icc (x - η) (x + η), P y := by
  obtain ⟨ρ, hρ, H⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ρ / 2, half_pos hρ, fun y hy => H ?_⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]

end CohenPriceFairness.LocalWelfare.Sol_market_profit_regular

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_market_profit_regular
open Filter Topology Asymptotics

theorem solution (m : Market) (hm : m.Admissible) (b : Prices)
    (hb : BaselineOptimal m b) (hr : LemmaRegularity m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i) :
    (∀ i, 0 < b i) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p → |p - b i| < ε) ∧
      (∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η))) ∧
      (∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - deriv (deriv (profit m i)) (b i) / 2 * h ^ 2)
        =o[𝓝 0] (fun h => h ^ 2)) ∧
      (∀ i, HasDerivAt (surplus m i) (-demand m i (b i)) (b i)) ∧
    (∀ i, 0 < demand m i (b i)) := by
  have hpos := l1_pos m hm b huniq
  have hb0 : ∀ i, 0 < b i := fun i => lt_of_le_of_lt hm.1 (hpos i).2.1
  have hev : ∀ i, ∀ᶠ y in 𝓝 (b i), ContinuousAt (profit m i) y :=
    fun i => (hr i).2.2.2.1.1.mono fun y hy => hy.continuousAt
  obtain ⟨η0, hη0, H0⟩ := l1_eta (b 0) (hev 0)
  obtain ⟨η1, hη1, H1⟩ := l1_eta (b 1) (hev 1)
  have hcont : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)) := by
    refine ⟨min η0 η1, lt_min hη0 hη1, fun i => ?_⟩
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hm0 := min_le_left η0 η1
    have hm1 := min_le_right η0 η1
    rcases hi with rfl | rfl
    · have hs : Set.Icc (b 0 - min η0 η1) (b 0 + min η0 η1) ⊆ Set.Icc (b 0 - η0) (b 0 + η0) :=
        Set.Icc_subset_Icc (by linarith) (by linarith)
      exact fun y hy => (H0 y (hs hy)).continuousWithinAt
    · have hs : Set.Icc (b 1 - min η0 η1) (b 1 + min η0 η1) ⊆ Set.Icc (b 1 - η1) (b 1 + η1) :=
        Set.Icc_subset_Icc (by linarith) (by linarith)
      exact fun y hy => (H1 y (hs hy)).continuousWithinAt
  have hcrit : ∀ i, deriv (profit m i) (b i) = 0 := by
    intro i
    have hmax : IsLocalMax (profit m i) (b i) := by
      filter_upwards [Ioi_mem_nhds (hb0 i)] with p hp
      exact (hb i).2 p (le_of_lt hp)
    exact hmax.deriv_eq_zero
  exact ⟨hb0, l1_loc m hm b hb huniq, hcont,
    fun i => l1_taylor _ _ (hr i).2.2.2.1 (hcrit i),
    fun i => l1_surplus_deriv m hm i (b i) (hr i).2.1.1.self_of_nhds,
    fun i => (hpos i).2.2⟩

