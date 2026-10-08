-- Prove2me | solution 1 for BalkemaDeHaan.ExpDomain.max_to_residual
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:34:14.081138+00:00
-- url     : https://prove2.me/submissions/04e42d7b-6850-47dd-ae82-5b869e1c2955

import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains



namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory Topology

lemma tail_eq_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) :
    BalkemaDeHaan.LimitTypes.tail μ y = 1 - cdf μ y := by
  unfold BalkemaDeHaan.LimitTypes.tail
  rw [cdf_eq_real, measureReal_def, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

lemma log_one_sub_bounds {u : ℝ} (hu1 : u < 1) :
    -u / (1 - u) ≤ Real.log (1 - u) ∧ Real.log (1 - u) ≤ -u := by
  have h1 : 0 < 1 - u := by linarith
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos h1
    have h2 : 1 - (1 - u)⁻¹ = -u / (1 - u) := by
      field_simp
      ring
    linarith
  · have := Real.log_le_sub_one_of_pos h1
    linarith

lemma continuous_lambdaLaw : Continuous lambdaLaw := by
  unfold lambdaLaw
  fun_prop

/-- Gnedenko's lemma: `F_n^n → e^{-τ}` iff `n (1 - F_n) → τ`, for `τ > 0`, `F_n ∈ [0,1]`. -/
lemma pow_tendsto_iff (F : ℕ → ℝ) (hF0 : ∀ n, 0 ≤ F n) (hF1 : ∀ n, F n ≤ 1) (τ : ℝ) (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => (F n) ^ n) atTop (𝓝 (Real.exp (-τ))) ↔
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - F n)) atTop (𝓝 τ) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  constructor
  · intro h
    -- eventually F n ^ n > 0
    have hpos : ∀ᶠ n in atTop, 0 < F n ^ n := h.eventually (lt_mem_nhds (Real.exp_pos _))
    have hFpos : ∀ᶠ n in atTop, 0 < F n := by
      filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
      rcases (hF0 n).lt_or_eq with h' | h'
      · exact h'
      · exfalso
        rw [← h', zero_pow (by omega)] at hn
        exact lt_irrefl _ hn
    -- n log F n → -τ
    have hlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (F n)) atTop (𝓝 (-τ)) := by
      have := (Real.continuousAt_log (Real.exp_pos (-τ)).ne').tendsto.comp h
      rw [Real.log_exp] at this
      refine this.congr' ?_
      filter_upwards with n
      simp [Function.comp, Real.log_pow]
    -- log F n → 0
    have hlog0 : Tendsto (fun n => Real.log (F n)) atTop (𝓝 0) := by
      have := hlog.div_atTop hnat
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    -- F n → 1
    have hF : Tendsto F atTop (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp hlog0
      rw [Real.exp_zero] at this
      refine this.congr' ?_
      filter_upwards [hFpos] with n hn
      simp [Function.comp, Real.exp_log hn]
    -- squeeze
    have hup : Tendsto (fun n : ℕ => -((n : ℝ) * Real.log (F n))) atTop (𝓝 τ) := by
      have := hlog.neg
      simpa using this
    have hlow : Tendsto (fun n : ℕ => F n * (-((n : ℝ) * Real.log (F n)))) atTop (𝓝 τ) := by
      have := hF.mul hup
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hFpos] with n hn
      obtain ⟨h1, _⟩ := log_one_sub_bounds (u := 1 - F n) (by linarith)
      have e : (1 : ℝ) - (1 - F n) = F n := by ring
      rw [e] at h1
      have h1' : -(1 - F n) ≤ Real.log (F n) * F n := by
        rw [div_le_iff₀ hn] at h1
        exact h1
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    · filter_upwards [hFpos] with n hn
      obtain ⟨_, h2⟩ := log_one_sub_bounds (u := 1 - F n) (by linarith)
      have e : (1 : ℝ) - (1 - F n) = F n := by ring
      rw [e] at h2
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
  · intro h
    -- u n → 0
    have hu : Tendsto (fun n => 1 - F n) atTop (𝓝 0) := by
      have := h.div_atTop hnat
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    have hFpos : ∀ᶠ n in atTop, 0 < F n := by
      have := hu.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
      filter_upwards [this] with n hn
      linarith
    have hF : Tendsto F atTop (𝓝 1) := by
      have := hu.const_sub 1
      simpa using this
    -- n log F n → -τ by squeeze
    have hup : Tendsto (fun n : ℕ => -((n : ℝ) * (1 - F n))) atTop (𝓝 (-τ)) := h.neg
    have hlow : Tendsto (fun n : ℕ => -((n : ℝ) * (1 - F n)) / F n) atTop (𝓝 (-τ)) := by
      have := hup.div hF one_ne_zero
      rw [div_one] at this
      exact this
    have hlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (F n)) atTop (𝓝 (-τ)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
      · filter_upwards [hFpos] with n hn
        obtain ⟨h1, _⟩ := log_one_sub_bounds (u := 1 - F n) (by linarith)
        have e : (1 : ℝ) - (1 - F n) = F n := by ring
        rw [e] at h1
        have hn0 : (0 : ℝ) ≤ n := by positivity
        rw [div_le_iff₀ hn] at h1 ⊢
        have : -((n:ℝ) * (1 - F n)) = n * (-(1 - F n)) := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_left h1 hn0
        linarith
      · filter_upwards [hFpos] with n hn
        obtain ⟨_, h2⟩ := log_one_sub_bounds (u := 1 - F n) (by linarith)
        have e : (1 : ℝ) - (1 - F n) = F n := by ring
        rw [e] at h2
        have hn0 : (0 : ℝ) ≤ n := by positivity
        nlinarith
    have := (Real.continuous_exp.tendsto _).comp hlog
    refine this.congr' ?_
    filter_upwards [hFpos] with n hn
    simp only [Function.comp]
    rw [← Real.log_pow, Real.exp_log (pow_pos hn n)]

theorem gnedenko_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    WeakConvergenceNat (fun n x => (cdf μ (a n * x + b n)) ^ n) lambdaLaw ↔
      TailScaledConvergence μ a b Set.univ := by
  unfold WeakConvergenceNat TailScaledConvergence
  have hL : ∀ x, ContinuousAt lambdaLaw x := fun x => continuous_lambdaLaw.continuousAt
  constructor
  · intro h x _
    have := h x (hL x)
    unfold lambdaLaw at this
    rw [pow_tendsto_iff _ (fun n => cdf_nonneg μ _) (fun n => cdf_le_one μ _) _ (Real.exp_pos _)] at this
    refine this.congr' ?_
    filter_upwards with n
    rw [tail_eq_one_sub_cdf]
    ring_nf
  · intro h x _
    have := h x (Set.mem_univ x)
    unfold lambdaLaw
    rw [pow_tendsto_iff _ (fun n => cdf_nonneg μ _) (fun n => cdf_le_one μ _) _ (Real.exp_pos _)]
    refine this.congr' ?_
    filter_upwards with n
    rw [tail_eq_one_sub_cdf]
    ring_nf


open Filter MeasureTheory ProbabilityTheory Topology

lemma tail_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Antitone (BalkemaDeHaan.LimitTypes.tail μ) := by
  intro x y hxy
  unfold BalkemaDeHaan.LimitTypes.tail
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ioi_subset_Ioi hxy))

lemma eventually_lt_of_antitone {R : ℝ → ℝ} (hR : Antitone R) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (p q : ℕ → ℝ) (α β : ℝ)
    (hp : Tendsto (fun n => c n * R (p n)) atTop (𝓝 α))
    (hq : Tendsto (fun n => c n * R (q n)) atTop (𝓝 β)) (hαβ : α < β) :
    ∀ᶠ n in atTop, q n < p n := by
  have h1 := hp.eventually (gt_mem_nhds (show α < (α + β) / 2 by linarith))
  have h2 := hq.eventually (lt_mem_nhds (show (α + β) / 2 < β by linarith))
  filter_upwards [h1, h2] with n hn1 hn2
  by_contra hcon
  push_neg at hcon
  have := mul_le_mul_of_nonneg_left (hR hcon) (hc n)
  linarith


/-- Squeeze principle with multiplicative tolerance, general filter. -/
lemma tendsto_of_exp_squeeze' {ι : Type*} (l : Filter ι) (f : ι → ℝ) (c : ℝ) (hc : 0 < c)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ lo up : ι → ℝ,
      Tendsto lo l (𝓝 (c * Real.exp (-ε))) ∧ Tendsto up l (𝓝 (c * Real.exp ε)) ∧
      ∀ᶠ i in l, lo i ≤ f i ∧ f i ≤ up i) :
    Tendsto f l (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcont : ContinuousAt (fun ε : ℝ => c * Real.exp (-ε)) 0 := by fun_prop
    have h0 : a < c * Real.exp (-0) := by simpa using ha
    have hev := hcont.eventually (lt_mem_nhds h0)
    have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < c * Real.exp (-ε) ∧ ε ∈ Set.Ioo (0 : ℝ) 1 :=
      (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (by norm_num))
    obtain ⟨ε, hε, hε0, hε1⟩ := hev2.exists
    obtain ⟨lo, up, hl, hu, hlu⟩ := h ε hε0 hε1
    filter_upwards [hl.eventually (lt_mem_nhds hε), hlu] with n hn hn2
    linarith [hn2.1]
  · intro a ha
    have hcont : ContinuousAt (fun ε : ℝ => c * Real.exp ε) 0 := by fun_prop
    have h0 : c * Real.exp 0 < a := by simpa using ha
    have hev := hcont.eventually (gt_mem_nhds h0)
    have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * Real.exp ε < a ∧ ε ∈ Set.Ioo (0 : ℝ) 1 :=
      (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (by norm_num))
    obtain ⟨ε, hε, hε0, hε1⟩ := hev2.exists
    obtain ⟨lo, up, hl, hu, hlu⟩ := h ε hε0 hε1
    filter_upwards [hu.eventually (gt_mem_nhds hε), hlu] with n hn hn2
    linarith [hn2.2]

lemma tail_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (hpositive : InDZero μ) (y : ℝ) :
    0 < BalkemaDeHaan.LimitTypes.tail μ y := by
  unfold BalkemaDeHaan.LimitTypes.tail
  exact ENNReal.toReal_pos (hpositive y).ne' (measure_ne_top μ _)

lemma tail_nonneg (μ : Measure ℝ) (y : ℝ) : 0 ≤ BalkemaDeHaan.LimitTypes.tail μ y :=
  ENNReal.toReal_nonneg

/-- The residual cdf for nonnegative abscissa, in terms of tails. -/
lemma residualCDF_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hpositive : InDZero μ) (t y : ℝ)
    (hy : 0 ≤ y) :
    BalkemaDeHaan.LimitTypes.residualCDF μ t y =
      1 - BalkemaDeHaan.LimitTypes.tail μ (t + y) / BalkemaDeHaan.LimitTypes.tail μ t := by
  unfold BalkemaDeHaan.LimitTypes.residualCDF BalkemaDeHaan.LimitTypes.tail
  have hsplit : μ (Set.Ioi t) = μ (Set.Ioc t (t + y)) + μ (Set.Ioi (t + y)) := by
    rw [← measure_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi,
      Set.Ioc_union_Ioi_eq_Ioi (by linarith)]
  have hpos : 0 < (μ (Set.Ioi t)).toReal := ENNReal.toReal_pos (hpositive t).ne' (measure_ne_top μ _)
  have h2 : (μ (Set.Ioi t)).toReal = (μ (Set.Ioc t (t + y))).toReal + (μ (Set.Ioi (t + y))).toReal := by
    rw [hsplit, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  rw [eq_sub_iff_add_eq, ← add_div, ← h2, div_self hpos.ne']

lemma residualCDF_nonpos (μ : Measure ℝ) (t y : ℝ) (hy : y ≤ 0) :
    BalkemaDeHaan.LimitTypes.residualCDF μ t y = 0 := by
  unfold BalkemaDeHaan.LimitTypes.residualCDF
  rw [Set.Ioc_eq_empty (by intro h; linarith), measure_empty, ENNReal.toReal_zero, zero_div]

theorem max_to_residual_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmax : InD μ lambdaLaw) (hpositive : InDZero μ) :
    InDr μ piLaw := by
  classical
  obtain ⟨a, b, ha, hweak⟩ := hmax
  have hT : TailScaledConvergence μ a b Set.univ := (gnedenko_core μ a b ha).1 hweak
  set R := BalkemaDeHaan.LimitTypes.tail μ with hRdef
  have hR : Antitone R := tail_antitone μ
  have hRpos : ∀ y, 0 < R y := tail_pos μ hpositive
  have hu : ∀ x : ℝ, Tendsto (fun n : ℕ => (n : ℝ) * R (b n + x * a n)) atTop (𝓝 (Real.exp (-x))) :=
    fun x => hT x (Set.mem_univ x)
  have hn0 : ∀ n : ℕ, (0 : ℝ) ≤ n := fun n => Nat.cast_nonneg n
  have hu0 : Tendsto (fun n : ℕ => (n : ℝ) * R (b n)) atTop (𝓝 1) := by
    have := hu 0
    simpa using this
  -- b n → ∞
  have hb_top : Tendsto b atTop atTop := by
    rw [tendsto_atTop]
    intro M
    have h1 := hu0.eventually (gt_mem_nhds (show (1:ℝ) < 2 by norm_num))
    have h2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (n : ℝ) * R M := by
      have : Tendsto (fun n : ℕ => (n : ℝ) * R M) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (hRpos M)
      exact this.eventually_ge_atTop 2
    filter_upwards [h1, h2] with n hn1 hn2
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_left (hR hcon.le) (hn0 n)
    linarith
  -- index function
  have hN : ∀ t : ℝ, ∃ n : ℕ, ∀ k ≥ n, t < b k := fun t =>
    eventually_atTop.1 (hb_top.eventually_gt_atTop t)
  set N : ℝ → ℕ := fun t => Nat.find (hN t) with hNdef
  have hN_spec : ∀ t, ∀ k ≥ N t, t < b k := fun t => Nat.find_spec (hN t)
  have hN_pos : ∀ t, b 0 ≤ t → 1 ≤ N t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have := hN_spec t 0 (by omega)
    linarith
  have hN_le : ∀ t, b 0 ≤ t → b (N t - 1) ≤ t := by
    intro t ht
    have h1 := hN_pos t ht
    have hmin : ¬ (∀ k ≥ N t - 1, t < b k) := Nat.find_min (hN t) (show N t - 1 < N t by omega)
    push_neg at hmin
    obtain ⟨k, hk, hkt⟩ := hmin
    rcases Nat.lt_or_ge k (N t) with hk' | hk'
    · have : k = N t - 1 := by omega
      rw [← this]; exact hkt
    · exact absurd (hN_spec t k hk') (not_lt.2 hkt)
  set n : ℝ → ℕ := fun t => N t - 1 with hndef
  have hn_le : ∀ t, b 0 ≤ t → b (n t) ≤ t := hN_le
  have hn_lt : ∀ t, b 0 ≤ t → t < b (n t + 1) := by
    intro t ht
    have h1 := hN_pos t ht
    have : n t + 1 = N t := by simp only [hndef]; omega
    rw [this]
    exact hN_spec t (N t) le_rfl
  have hn_top : Tendsto n atTop atTop := by
    rw [tendsto_atTop]
    intro M
    filter_upwards [eventually_ge_atTop (b (M + 1)), eventually_ge_atTop (b 0)] with t ht ht0
    by_contra hcon
    push_neg at hcon
    have : N t ≤ M + 1 := by simp only [hndef] at hcon; omega
    have := hN_spec t (M + 1) this
    linarith
  -- comparison: b (n+1) < b n + ε a n eventually
  have hw : ∀ y : ℝ, Tendsto (fun k : ℕ => (k : ℝ) * R (b (k + 1) + y * a (k + 1))) atTop (𝓝 (Real.exp (-y))) := by
    intro y
    have h1 := (hu y).comp (tendsto_add_atTop_nat 1)
    have h2 := (tendsto_natCast_div_add_atTop (1 : ℝ)).mul h1
    rw [one_mul] at h2
    refine h2.congr' ?_
    filter_upwards with k
    simp only [Function.comp]
    have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [this]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hcmp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, b (k + 1) < b k + ε * a k := by
    intro ε hε
    have := eventually_lt_of_antitone hR (fun k => (k : ℝ)) hn0 (fun k => b k + ε * a k)
      (fun k => b (k + 1) + 0 * a (k + 1)) _ _ (hu ε) (hw 0) (Real.exp_lt_exp.2 (by linarith))
    filter_upwards [this] with k hk
    simpa using hk
  refine ⟨hpositive, fun t => a (n t), fun _ => 0, fun t => ha (n t), ?_⟩
  intro x _
  simp only [zero_add]
  rcases le_or_gt x 0 with hx | hx
  · have hPi : piLaw x = 0 := by
      unfold piLaw
      split_ifs with h
      · rfl
      · have : x = 0 := le_antisymm hx (not_lt.1 h)
        rw [this]; simp
    rw [hPi]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with t
    have := residualCDF_nonpos μ t (x * a (n t)) (mul_nonpos_of_nonpos_of_nonneg hx (ha (n t)).le)
    rw [← this]
  · have hPi : piLaw x = 1 - Real.exp (-x) := by
      unfold piLaw
      rw [if_neg (not_lt.2 hx.le)]
    rw [hPi]
    have hkey : Tendsto (fun t => R (t + x * a (n t)) / R t) atTop (𝓝 (Real.exp (-x))) := by
      refine tendsto_of_exp_squeeze' atTop _ _ (Real.exp_pos _) ?_
      intro ε hε0 hε1
      refine ⟨fun t => ((n t : ℕ) : ℝ) * R (b (n t) + (x + ε) * a (n t)) / (((n t : ℕ) : ℝ) * R (b (n t))),
        fun t => ((n t : ℕ) : ℝ) * R (b (n t) + x * a (n t)) / (((n t : ℕ) : ℝ) * R (b (n t) + ε * a (n t))),
        ?_, ?_, ?_⟩
      · have := ((hu (x + ε)).comp hn_top).div (hu0.comp hn_top) one_ne_zero
        rw [div_one, show -(x + ε) = -x + -ε by ring, Real.exp_add] at this
        exact this
      · have := ((hu x).comp hn_top).div ((hu ε).comp hn_top) (Real.exp_pos _).ne'
        rw [show Real.exp (-x) / Real.exp (-ε) = Real.exp (-x) * Real.exp ε by
          rw [Real.exp_neg ε, div_inv_eq_mul]] at this
        exact this
      · filter_upwards [hn_top.eventually (hcmp ε hε0), hn_top.eventually (eventually_ge_atTop 1),
          eventually_ge_atTop (b 0)] with t ht1 ht2 ht0
        have hle := hn_le t ht0
        have hlt := hn_lt t ht0
        have hnpos : (0 : ℝ) < ((n t : ℕ) : ℝ) := by exact_mod_cast ht2
        have hant := ha (n t)
        rw [mul_div_mul_left _ _ hnpos.ne', mul_div_mul_left _ _ hnpos.ne']
        constructor
        · apply div_le_div₀ (tail_nonneg μ _) (hR (by nlinarith)) (hRpos _) (hR hle)
        · apply div_le_div₀ (tail_nonneg μ _) (hR (by nlinarith)) (hRpos _) (hR (by linarith))
    have := hkey.const_sub 1
    refine this.congr' ?_
    filter_upwards with t
    exact (residualCDF_eq μ hpositive t (x * a (n t)) (mul_nonneg hx.le (ha (n t)).le)).symm

end BalkemaDeHaan.ExpDomain

open BalkemaDeHaan.ExpDomain
open MeasureTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmax : InD μ lambdaLaw) (hpositive : InDZero μ) :
    InDr μ piLaw := by
  exact max_to_residual_core μ hmax hpositive
