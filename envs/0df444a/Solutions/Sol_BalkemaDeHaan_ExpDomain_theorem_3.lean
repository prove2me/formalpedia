-- Prove2me | solution 1 for BalkemaDeHaan.ExpDomain.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:47:38.500286+00:00
-- url     : https://prove2.me/submissions/7990ba8d-0b05-4435-b9cf-435ea8ec4f95

import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains



namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory Topology

lemma tail_eq_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) :
    BalkemaDeHaan.LimitTypes.tail μ y = 1 - cdf μ y := by
  unfold BalkemaDeHaan.LimitTypes.tail
  rw [cdf_eq_real, measureReal_def, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

lemma tail_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Antitone (BalkemaDeHaan.LimitTypes.tail μ) := by
  intro x y hxy
  unfold BalkemaDeHaan.LimitTypes.tail
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ioi_subset_Ioi hxy))

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


open Filter MeasureTheory ProbabilityTheory Topology

/-- Monotone functions converging pointwise to a continuous distribution function have
uniformly small jumps eventually. -/
lemma uniform_small_jumps (G : ℝ → ℝ) (hG : Continuous G) (hG0 : Tendsto G atBot (𝓝 0))
    (hG1 : Tendsto G atTop (𝓝 1)) (H : ℝ → ℝ → ℝ) (hmono : ∀ t, Monotone (H t))
    (h0 : ∀ t u, 0 ≤ H t u) (h1 : ∀ t u, H t u ≤ 1)
    (hconv : ∀ z, Tendsto (fun t => H t z) atTop (𝓝 (G z))) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ u : ℝ, ∃ u' < u, H t u - H t u' ≤ ε := by
  obtain ⟨z0, hz0⟩ : ∃ z0, G z0 < ε / 4 :=
    (hG0.eventually (gt_mem_nhds (show (0:ℝ) < ε / 4 by positivity))).exists
  obtain ⟨z1, hz1⟩ : ∃ z1, ∀ z ≥ z1, 1 - ε / 4 < G z :=
    eventually_atTop.1 (hG1.eventually (lt_mem_nhds (show 1 - ε / 4 < (1:ℝ) by linarith)))
  set zk := max z1 (z0 + 1) with hzk
  have hzk1 : 1 - ε / 4 < G zk := hz1 zk (le_max_left _ _)
  have hz0k : z0 < zk := by linarith [le_max_right z1 (z0 + 1)]
  have hUC : UniformContinuousOn G (Set.Icc z0 zk) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hG.continuousOn
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.1 hUC (ε / 4) (by positivity)
  set M : ℕ := ⌈2 * (zk - z0) / δ⌉₊ + 1 with hM
  have hMpos : (0:ℝ) < M := by rw [hM]; positivity
  set hstep := (zk - z0) / M with hh
  have hhpos : 0 < hstep := by rw [hh]; exact div_pos (by linarith) hMpos
  have hhδ : hstep < δ := by
    rw [hh, div_lt_iff₀ hMpos]
    have h1 : 2 * (zk - z0) / δ ≤ ⌈2 * (zk - z0) / δ⌉₊ := Nat.le_ceil _
    have hM' : (M:ℝ) = ⌈2 * (zk - z0) / δ⌉₊ + 1 := by rw [hM]; push_cast; ring
    rw [hM']
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  set p : ℕ → ℝ := fun i => z0 + i * hstep with hp
  have hpM : p M = zk := by
    have e : (M:ℝ) * ((zk - z0) / M) = zk - z0 := by field_simp
    simp only [hp]
    rw [hh, e]
    ring
  have hp0 : p 0 = z0 := by simp [hp]
  have hev : ∀ᶠ t in atTop, ∀ i ∈ Finset.range (M + 1), |H t (p i) - G (p i)| < ε / 4 := by
    rw [eventually_all_finset]
    intro i _
    have := (hconv (p i)).eventually
      (Metric.ball_mem_nhds (G (p i)) (show (0:ℝ) < ε / 4 by positivity))
    filter_upwards [this] with t ht
    rw [Real.dist_eq] at ht
    exact ht
  filter_upwards [hev] with t ht
  intro u
  rcases le_or_gt u z0 with hu | hu
  · refine ⟨u - 1, by linarith, ?_⟩
    have h1' := ht 0 (by simp)
    rw [hp0, abs_lt] at h1'
    have := hmono t hu
    have := h0 t (u - 1)
    linarith
  rcases lt_or_ge zk u with hu' | hu'
  · refine ⟨zk, hu', ?_⟩
    have h1' := ht M (by simp)
    rw [hpM, abs_lt] at h1'
    have := h1 t u
    linarith
  · set r := (u - z0) / hstep with hr
    have hrpos : 0 < r := by rw [hr]; exact div_pos (by linarith) hhpos
    have hc : 0 < ⌈r⌉₊ := Nat.ceil_pos.2 hrpos
    obtain ⟨i, hi⟩ : ∃ i, ⌈r⌉₊ = i + 1 := ⟨⌈r⌉₊ - 1, by omega⟩
    have hi1 : (i : ℝ) < r := by
      have := Nat.ceil_lt_add_one hrpos.le
      rw [hi] at this; push_cast at this; linarith
    have hi2 : r ≤ (i : ℝ) + 1 := by
      have := Nat.le_ceil r
      rw [hi] at this; push_cast at this; exact this
    have hiM : i + 1 ≤ M := by
      rw [← hi, Nat.ceil_le, hr, div_le_iff₀ hhpos, hh]
      rw [mul_div_assoc', le_div_iff₀ hMpos]
      nlinarith
    have hpi : p i < u := by
      simp only [hp]
      rw [hr, lt_div_iff₀ hhpos] at hi1
      linarith
    have hpi1 : u ≤ p (i + 1) := by
      simp only [hp]
      rw [hr, div_le_iff₀ hhpos] at hi2
      push_cast
      linarith
    refine ⟨p i, hpi, ?_⟩
    have ha := ht i (by simp; omega)
    have hb := ht (i + 1) (by simp; omega)
    have hmo := hmono t hpi1
    have hpi_mem : p i ∈ Set.Icc z0 zk := by
      refine ⟨?_, by linarith⟩
      simp only [hp]
      have := mul_nonneg (Nat.cast_nonneg i) hhpos.le
      linarith
    have hpi1_mem : p (i + 1) ∈ Set.Icc z0 zk := by
      refine ⟨by linarith, ?_⟩
      rw [← hpM]
      simp only [hp]
      have : ((i : ℝ) + 1) ≤ M := by exact_mod_cast hiM
      push_cast
      nlinarith
    have hdist : |G (p (i + 1)) - G (p i)| < ε / 4 := by
      have := hδG _ hpi1_mem _ hpi_mem (by
        rw [Real.dist_eq]
        simp only [hp]
        push_cast
        rw [show z0 + ((i:ℝ) + 1) * hstep - (z0 + i * hstep) = hstep by ring, abs_of_pos hhpos]
        exact hhδ)
      rw [Real.dist_eq] at this
      exact this
    rw [abs_lt] at ha hb hdist
    linarith

lemma residualCDF_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Monotone (BalkemaDeHaan.LimitTypes.residualCDF μ t) := by
  intro u v huv
  unfold BalkemaDeHaan.LimitTypes.residualCDF
  apply div_le_div_of_nonneg_right _ ENNReal.toReal_nonneg
  exact ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono (Set.Ioc_subset_Ioc_right (by linarith)))

lemma residualCDF_nonneg' (μ : Measure ℝ) (t u : ℝ) :
    0 ≤ BalkemaDeHaan.LimitTypes.residualCDF μ t u :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma residualCDF_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t u : ℝ) :
    BalkemaDeHaan.LimitTypes.residualCDF μ t u ≤ 1 := by
  unfold BalkemaDeHaan.LimitTypes.residualCDF
  apply div_le_one_of_le₀ _ ENNReal.toReal_nonneg
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono Set.Ioc_subset_Ioi_self)

/-- An atom at `t + u` forces a jump of the residual cdf. -/
lemma atom_le_jump (μ : Measure ℝ) [IsProbabilityMeasure μ] (t u u' : ℝ) (hu : 0 < u) (hu' : u' < u)
    (hpos : 0 < BalkemaDeHaan.LimitTypes.tail μ t) :
    (μ {t + u}).toReal / BalkemaDeHaan.LimitTypes.tail μ t ≤
      BalkemaDeHaan.LimitTypes.residualCDF μ t u - BalkemaDeHaan.LimitTypes.residualCDF μ t u' := by
  have htail : (μ (Set.Ioi t)).toReal = BalkemaDeHaan.LimitTypes.tail μ t := rfl
  unfold BalkemaDeHaan.LimitTypes.residualCDF
  rw [htail, ← sub_div, div_le_div_iff_of_pos_right hpos]
  have hdisj : Disjoint (Set.Ioc t (t + u')) {t + u} := by
    rw [Set.disjoint_singleton_right]
    intro h
    exact absurd h.2 (by linarith)
  have hsub : Set.Ioc t (t + u') ∪ {t + u} ⊆ Set.Ioc t (t + u) := by
    intro y hy
    rcases hy with hy | hy
    · exact ⟨hy.1, by linarith [hy.2]⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact ⟨by linarith, le_rfl⟩
  have := measure_mono (μ := μ) hsub
  rw [measure_union hdisj (measurableSet_singleton _)] at this
  have h2 := ENNReal.toReal_mono (measure_ne_top μ _) this
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h2
  linarith

lemma Ici_split (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    (μ (Set.Ici x)).toReal = (μ {x}).toReal + BalkemaDeHaan.LimitTypes.tail μ x := by
  unfold BalkemaDeHaan.LimitTypes.tail
  have : Set.Ici x = {x} ∪ Set.Ioi x := by
    ext y
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · intro h
      rcases eq_or_lt_of_le h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact h.ge
      · exact h.le
  rw [this, measure_union (Set.disjoint_singleton_left.2 Set.self_notMem_Ioi) measurableSet_Ioi,
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]

lemma Ioi_split (μ : Measure ℝ) [IsProbabilityMeasure μ] (x δ : ℝ) (hδ : 0 < δ) :
    BalkemaDeHaan.LimitTypes.tail μ (x - δ) =
      (μ (Set.Ioo (x - δ) x)).toReal + (μ (Set.Ici x)).toReal := by
  unfold BalkemaDeHaan.LimitTypes.tail
  have hdisj : Disjoint (Set.Ioo (x - δ) x) (Set.Ici x) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact absurd hy.2 (not_lt.2 hy')
  rw [← Set.Ioo_union_Ici_eq_Ioi (show x - δ < x by linarith), measure_union hdisj measurableSet_Ici,
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]

lemma tendsto_Ioo_shrink (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    Tendsto (fun k : ℕ => (μ (Set.Ioo (x - 1 / ((k : ℝ) + 1)) x)).toReal) atTop (𝓝 0) := by
  have hanti : Antitone (fun k : ℕ => Set.Ioo (x - 1 / ((k : ℝ) + 1)) x) := by
    intro k k' hkk'
    apply Set.Ioo_subset_Ioo_left
    have : (1 : ℝ) / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
      linarith
    linarith
  have hempty : (⋂ k : ℕ, Set.Ioo (x - 1 / ((k : ℝ) + 1)) x) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false, not_forall]
    by_contra hcon
    push_neg at hcon
    have hy : y < x := (hcon 0).2
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < x - y by linarith)
    have := (hcon n).1
    linarith
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun k => measurableSet_Ioo.nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
  rw [hempty, measure_empty] at h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at h2
  exact h2

/-- Lemma 3 core: the atom at `x` is negligible relative to the tail. -/
lemma atom_ratio_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ] (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : Tendsto G atBot (𝓝 0)) (hG1 : Tendsto G atTop (𝓝 1)) (h : InDr μ G) :
    Tendsto (fun x => (μ {x}).toReal / BalkemaDeHaan.LimitTypes.tail μ x) atTop (𝓝 0) := by
  obtain ⟨hpos, α, β, hα, hconv⟩ := h
  set R := BalkemaDeHaan.LimitTypes.tail μ with hRdef
  have hRpos : ∀ y, 0 < R y := fun y =>
    ENNReal.toReal_pos (hpos y).ne' (measure_ne_top μ _)
  set H : ℝ → ℝ → ℝ := fun t z => BalkemaDeHaan.LimitTypes.residualCDF μ t (β t + z * α t) with hH
  have hmono : ∀ t, Monotone (H t) := by
    intro t z z' hzz'
    simp only [hH]
    apply residualCDF_mono μ t
    have := hα t
    nlinarith
  have hconv' : ∀ z, Tendsto (fun t => H t z) atTop (𝓝 (G z)) := fun z =>
    hconv z (hG.continuousAt)
  -- key estimate
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ᶠ x in atTop, (μ {x}).toReal / R x ≤ 2 * ε := by
    intro ε hε hε2
    have hev := uniform_small_jumps G hG hG0 hG1 H hmono (fun t u => residualCDF_nonneg' μ _ _)
      (fun t u => residualCDF_le_one μ _ _) hconv' ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.1 hev
    filter_upwards [eventually_ge_atTop (T + 1)] with x hx
    -- for each k, μ{x} ≤ ε R(x - 1/(k+1))
    have hk : ∀ k : ℕ, (μ {x}).toReal ≤ ε * ((μ (Set.Ioo (x - 1 / ((k : ℝ) + 1)) x)).toReal + (μ (Set.Ici x)).toReal) := by
      intro k
      set δ : ℝ := 1 / ((k : ℝ) + 1) with hδ
      have hδpos : 0 < δ := by positivity
      have hδ1 : δ ≤ 1 := by
        rw [hδ, div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) k]
      set t := x - δ with ht
      have htT : T ≤ t := by rw [ht]; linarith
      obtain ⟨z', hz', hjump⟩ := hT t htT ((δ - β t) / α t)
      have hαt := hα t
      have e1 : β t + (δ - β t) / α t * α t = δ := by field_simp; ring
      simp only [hH] at hjump
      rw [e1] at hjump
      have hu' : β t + z' * α t < δ := by
        have := (lt_div_iff₀ hαt).1 hz'
        linarith
      have hA := atom_le_jump μ t δ (β t + z' * α t) hδpos hu' (hRpos t)
      have hxt : t + δ = x := by rw [ht]; ring
      rw [hxt] at hA
      have hB : (μ {x}).toReal ≤ ε * R t := by
        rw [div_le_iff₀ (hRpos t)] at hA
        nlinarith [hRpos t]
      rw [ht, hRdef, Ioi_split μ x δ hδpos] at hB
      exact hB
    have hlim : Tendsto (fun k : ℕ => ε * ((μ (Set.Ioo (x - 1 / ((k : ℝ) + 1)) x)).toReal + (μ (Set.Ici x)).toReal)) atTop
        (𝓝 (ε * (0 + (μ (Set.Ici x)).toReal))) :=
      tendsto_const_nhds.mul ((tendsto_Ioo_shrink μ x).add tendsto_const_nhds)
    have hfinal : (μ {x}).toReal ≤ ε * (0 + (μ (Set.Ici x)).toReal) := ge_of_tendsto' hlim hk
    rw [zero_add, Ici_split μ x] at hfinal
    rw [div_le_iff₀ (hRpos x)]
    nlinarith [hRpos x, ENNReal.toReal_nonneg (a := μ {x})]
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards with x
    exact lt_of_lt_of_le ha (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  · intro a ha
    have hε : 0 < min (a / 4) (1 / 4) := lt_min (by positivity) (by norm_num)
    filter_upwards [key (min (a / 4) (1 / 4)) hε (by linarith [min_le_right (a / 4) (1 / 4 : ℝ)])] with x hx
    linarith [min_le_left (a / 4) (1 / 4 : ℝ)]

lemma continuous_cdf_tendsto (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Tendsto (fun x => (cdf ν) x) atBot (𝓝 0) ∧ Tendsto (fun x => (cdf ν) x) atTop (𝓝 1) :=
  ⟨tendsto_cdf_atBot ν, tendsto_cdf_atTop ν⟩

theorem lemma_3_core (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hG : Continuous (cdf ν)) (h : InDr μ (cdf ν)) :
    Tendsto (fun x : ℝ => (μ (Set.Ici x)).toReal / BalkemaDeHaan.LimitTypes.tail μ x) atTop (nhds 1) := by
  have hpos := h.1
  have hRpos : ∀ y, 0 < BalkemaDeHaan.LimitTypes.tail μ y := fun y =>
    ENNReal.toReal_pos (hpos y).ne' (measure_ne_top μ _)
  have hatom := atom_ratio_tendsto μ (fun x => (cdf ν) x) hG (tendsto_cdf_atBot ν) (tendsto_cdf_atTop ν) h
  have := hatom.const_add 1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards with x
  rw [Ici_split μ x, add_div, div_self (hRpos x).ne', add_comm]


lemma piLaw_eq_max : piLaw = fun x => max 0 (1 - Real.exp (-x)) := by
  funext x
  unfold piLaw
  split_ifs with h
  · symm
    apply max_eq_left
    have : 1 < Real.exp (-x) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by linarith)
    linarith
  · symm
    apply max_eq_right
    have : Real.exp (-x) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by linarith)
    linarith

lemma continuous_piLaw : Continuous piLaw := by
  rw [piLaw_eq_max]
  fun_prop

lemma piLaw_atBot : Tendsto piLaw atBot (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  unfold piLaw
  rw [if_pos hx]

lemma piLaw_atTop : Tendsto piLaw atTop (𝓝 1) := by
  have : Tendsto (fun x : ℝ => 1 - Real.exp (-x)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  unfold piLaw
  rw [if_neg (not_lt.2 hx)]

/-- Quantile-type sequence `t n` with `n R(t n) → 1` and `t n → ∞`. -/
lemma exists_quantile_seq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hpos : InDZero μ)
    (hatom : Tendsto (fun x => (μ {x}).toReal / BalkemaDeHaan.LimitTypes.tail μ x) atTop (𝓝 0)) :
    ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) * BalkemaDeHaan.LimitTypes.tail μ (t n)) atTop (𝓝 1) := by
  classical
  set R := BalkemaDeHaan.LimitTypes.tail μ with hRdef
  have hR : Antitone R := tail_antitone μ
  have hRpos : ∀ y, 0 < R y := tail_pos μ hpos
  have hRcdf : ∀ y, R y = 1 - cdf μ y := tail_eq_one_sub_cdf μ
  set S : ℕ → Set ℝ := fun n => {x | R x ≤ 1 / n} with hS
  set t : ℕ → ℝ := fun n => sInf (S n) with ht
  have hSne : ∀ n : ℕ, 1 ≤ n → (S n).Nonempty := by
    intro n hn
    have hn' : (0:ℝ) < 1 / n := by positivity
    have := (tendsto_cdf_atTop μ).eventually (lt_mem_nhds (show 1 - 1 / (n:ℝ) < 1 by linarith))
    obtain ⟨x, hx⟩ := this.exists
    exact ⟨x, by simp only [hS, Set.mem_setOf_eq]; rw [hRcdf]; linarith⟩
  have hSbdd : ∀ n : ℕ, 2 ≤ n → BddBelow (S n) := by
    intro n hn
    have hn2 : (1:ℝ) / n ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hn
    have := (tendsto_cdf_atBot μ).eventually (gt_mem_nhds (show (0:ℝ) < 1 / 2 by norm_num))
    obtain ⟨y, hy⟩ := this.exists
    refine ⟨y, ?_⟩
    intro x hx
    simp only [hS, Set.mem_setOf_eq] at hx
    by_contra hcon
    push_neg at hcon
    have := hR hcon.le
    rw [hRcdf y] at this
    linarith
  have hSup : ∀ n, ∀ x ∈ S n, ∀ x', x ≤ x' → x' ∈ S n := by
    intro n x hx x' hxx'
    simp only [hS, Set.mem_setOf_eq] at hx ⊢
    exact le_trans (hR hxx') hx
  -- upper bound: R (t n) ≤ 1/n for n ≥ 2
  have hup : ∀ n : ℕ, 2 ≤ n → R (t n) ≤ 1 / n := by
    intro n hn
    have hne := hSne n (by omega)
    have hbdd := hSbdd n hn
    have hgt : ∀ x, t n < x → R x ≤ 1 / n := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx
      exact hSup n s hs x hsx.le
    have hcont : ContinuousWithinAt (fun y => (cdf μ) y) (Set.Ici (t n)) (t n) :=
      (cdf μ).right_continuous (t n)
    have hcont' : Tendsto (fun y => (cdf μ) y) (𝓝[>] (t n)) (𝓝 ((cdf μ) (t n))) :=
      hcont.tendsto.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    have hge : 1 - 1 / (n:ℝ) ≤ (cdf μ) (t n) := by
      apply ge_of_tendsto hcont'
      filter_upwards [self_mem_nhdsWithin] with y hy
      have := hgt y hy
      rw [hRcdf] at this
      linarith
    rw [hRcdf]
    linarith
  -- lower bound: μ(Ici (t n)) ≥ 1/n for n ≥ 2
  have hlow : ∀ n : ℕ, 2 ≤ n → 1 / (n:ℝ) ≤ (μ (Set.Ici (t n))).toReal := by
    intro n hn
    have hne := hSne n (by omega)
    have hbdd := hSbdd n hn
    have hlt : ∀ y, y < t n → 1 / (n:ℝ) < R y := by
      intro y hy
      by_contra hcon
      push_neg at hcon
      have : y ∈ S n := by simp only [hS, Set.mem_setOf_eq]; exact hcon
      have := csInf_le hbdd this
      linarith
    have hlim : Tendsto (fun k : ℕ => (μ (Set.Ioo (t n - 1 / ((k:ℝ) + 1)) (t n))).toReal + (μ (Set.Ici (t n))).toReal)
        atTop (𝓝 (0 + (μ (Set.Ici (t n))).toReal)) :=
      (tendsto_Ioo_shrink μ (t n)).add tendsto_const_nhds
    rw [zero_add] at hlim
    apply ge_of_tendsto' hlim
    intro k
    have hδ : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
    rw [← Ioi_split μ (t n) _ hδ]
    exact (hlt _ (by linarith)).le
  -- t n → ∞
  have ht_top : Tendsto t atTop atTop := by
    rw [tendsto_atTop]
    intro M
    have h1 := tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / R M)
    filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
    by_contra hcon
    push_neg at hcon
    have h2 := hR hcon.le
    have h3 := hup n hn2
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h4 : 1 / (n:ℝ) ≤ R M / 2 := by
      rw [div_le_iff₀ hnpos]
      rw [div_le_iff₀ (hRpos M)] at hn
      linarith
    linarith [hRpos M]
  refine ⟨t, ht_top, ?_⟩
  -- squeeze
  have hlo : Tendsto (fun n : ℕ => (1 + (μ {t n}).toReal / R (t n))⁻¹) atTop (𝓝 1) := by
    have := ((hatom.comp ht_top).const_add 1).inv₀ (by norm_num)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hI := hlow n hn
    have hIci := Ici_split μ (t n)
    have hRp := hRpos (t n)
    have hIpos : 0 < (μ (Set.Ici (t n))).toReal := by linarith [ENNReal.toReal_nonneg (a := μ {t n})]
    have e : (1 + (μ {t n}).toReal / R (t n))⁻¹ = R (t n) / (μ (Set.Ici (t n))).toReal := by
      rw [hIci, ← hRdef, add_comm (μ {t n}).toReal]
      field_simp
    rw [e, div_le_iff₀ hIpos]
    rw [div_le_iff₀ hnpos] at hI
    nlinarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have := hup n hn
    rw [le_div_iff₀ hnpos] at this
    linarith

theorem equation_11_positive_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : InDr μ piLaw) :
    ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧
      TailScaledConvergence μ a b (Set.Ioi 0) := by
  have hatom := atom_ratio_tendsto μ piLaw continuous_piLaw piLaw_atBot piLaw_atTop h
  obtain ⟨hpos, α, β, hα, hconv⟩ := h
  obtain ⟨t, ht_top, hnt⟩ := exists_quantile_seq μ hpos hatom
  set R := BalkemaDeHaan.LimitTypes.tail μ with hRdef
  have hRpos : ∀ y, 0 < R y := tail_pos μ hpos
  refine ⟨fun n => α (t n), fun n => t n + β (t n), fun n => hα (t n), ?_⟩
  intro x hx
  simp only [Set.mem_Ioi] at hx
  have hc := (hconv x continuous_piLaw.continuousAt).comp ht_top
  have hPi : piLaw x = 1 - Real.exp (-x) := by
    unfold piLaw
    rw [if_neg (not_lt.2 hx.le)]
  rw [hPi] at hc
  have hev : ∀ᶠ n in atTop, 0 < β (t n) + x * α (t n) := by
    have hpos' : 0 < 1 - Real.exp (-x) := by
      have : Real.exp (-x) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.2 (by linarith)
      linarith
    filter_upwards [hc.eventually (lt_mem_nhds hpos')] with n hn
    by_contra hcon
    push_neg at hcon
    simp only [Function.comp] at hn
    rw [residualCDF_nonpos μ _ _ hcon] at hn
    linarith
  have hratio : Tendsto (fun n => R (t n + (β (t n) + x * α (t n))) / R (t n)) atTop (𝓝 (Real.exp (-x))) := by
    have := hc.const_sub 1
    rw [show 1 - (1 - Real.exp (-x)) = Real.exp (-x) by ring] at this
    refine this.congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp]
    rw [residualCDF_eq μ hpos _ _ hn.le]
    ring
  have := hnt.mul hratio
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards with n
  have hRp := (hRpos (t n)).ne'
  rw [hRdef] at hRp ⊢
  field_simp
  ring_nf

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

/-- `n / (n / K) → K` for the natural-number quotient. -/
lemma tendsto_div_natDiv (K : ℕ) (hK : 0 < K) :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n / K : ℕ) : ℝ)) atTop (𝓝 (K : ℝ)) := by
  have hq : Tendsto (fun n : ℕ => n / K) atTop atTop := Nat.tendsto_div_const_atTop hK.ne'
  have hup : Tendsto (fun n : ℕ => (K : ℝ) + (K : ℝ) / ((n / K : ℕ) : ℝ)) atTop (𝓝 ((K : ℝ) + 0)) :=
    tendsto_const_nhds.add ((tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)).comp hq)
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop K] with n hn
    have hq1 : 1 ≤ n / K := (Nat.one_le_div_iff hK).2 hn
    have hqpos : (0 : ℝ) < ((n / K : ℕ) : ℝ) := by exact_mod_cast hq1
    rw [le_div_iff₀ hqpos]
    have : K * (n / K) ≤ n := Nat.mul_div_le n K
    exact_mod_cast this
  · filter_upwards [eventually_ge_atTop K] with n hn
    have hq1 : 1 ≤ n / K := (Nat.one_le_div_iff hK).2 hn
    have hqpos : (0 : ℝ) < ((n / K : ℕ) : ℝ) := by exact_mod_cast hq1
    rw [div_le_iff₀ hqpos]
    have e : ((K : ℝ) + K / ((n / K : ℕ) : ℝ)) * ((n / K : ℕ) : ℝ) = K * ((n / K : ℕ) : ℝ) + K := by
      field_simp
    rw [e]
    have h1 : n = K * (n / K) + n % K := (Nat.div_add_mod n K).symm
    have h2 : n % K < K := Nat.mod_lt n hK
    have h3 : (n : ℝ) = K * ((n / K : ℕ) : ℝ) + ((n % K : ℕ) : ℝ) := by exact_mod_cast h1
    have h4 : ((n % K : ℕ) : ℝ) ≤ K := by exact_mod_cast h2.le
    rw [h3]
    linarith

/-- Squeeze principle with multiplicative tolerance. -/
lemma tendsto_of_exp_squeeze (f : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ l u : ℕ → ℝ,
      Tendsto l atTop (𝓝 (c * Real.exp (-ε))) ∧ Tendsto u atTop (𝓝 (c * Real.exp ε)) ∧
      ∀ᶠ n in atTop, l n ≤ f n ∧ f n ≤ u n) :
    Tendsto f atTop (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcont : ContinuousAt (fun ε : ℝ => c * Real.exp (-ε)) 0 := by fun_prop
    have h0 : a < c * Real.exp (-0) := by simpa using ha
    have hev := hcont.eventually (lt_mem_nhds h0)
    have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < c * Real.exp (-ε) ∧ ε ∈ Set.Ioo (0 : ℝ) 1 :=
      (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (by norm_num))
    obtain ⟨ε, hε, hε0, hε1⟩ := hev2.exists
    obtain ⟨l, u, hl, hu, hlu⟩ := h ε hε0 hε1
    filter_upwards [hl.eventually (lt_mem_nhds hε), hlu] with n hn hn2
    linarith [hn2.1]
  · intro a ha
    have hcont : ContinuousAt (fun ε : ℝ => c * Real.exp ε) 0 := by fun_prop
    have h0 : c * Real.exp 0 < a := by simpa using ha
    have hev := hcont.eventually (gt_mem_nhds h0)
    have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * Real.exp ε < a ∧ ε ∈ Set.Ioo (0 : ℝ) 1 :=
      (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (by norm_num))
    obtain ⟨ε, hε, hε0, hε1⟩ := hev2.exists
    obtain ⟨l, u, hl, hu, hlu⟩ := h ε hε0 hε1
    filter_upwards [hu.eventually (gt_mem_nhds hε), hlu] with n hn hn2
    linarith [hn2.2]

theorem equation_11_all_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h : TailScaledConvergence μ a b (Set.Ioi 0)) :
    TailScaledConvergence μ a b Set.univ := by
  intro x₀ _
  rcases lt_or_ge 0 x₀ with hx | hx
  · exact h x₀ hx
  set R := BalkemaDeHaan.LimitTypes.tail μ with hRdef
  have hR : Antitone R := tail_antitone μ
  have hu : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * R (b n + x * a n)) atTop (𝓝 (Real.exp (-x))) :=
    fun x hx => h x hx
  -- choose K
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (1 - x₀))
  have hKpos : (0 : ℝ) < K := lt_trans (Real.exp_pos _) hK
  have hKnat : 0 < K := by exact_mod_cast hKpos
  set L := Real.log K with hL
  have hL1 : 1 - x₀ < L := by
    rw [hL]
    exact (Real.lt_log_iff_exp_lt hKpos).2 hK
  have hexpL : Real.exp L = K := Real.exp_log hKpos
  set m : ℕ → ℕ := fun n => n / K with hm
  have hm_top : Tendsto m atTop atTop := Nat.tendsto_div_const_atTop hKnat.ne'
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((m n : ℕ) : ℝ)) atTop (𝓝 (K : ℝ)) :=
    tendsto_div_natDiv K hKnat
  -- v_n(y) → K e^{-y}
  have hv : ∀ y : ℝ, 0 < y →
      Tendsto (fun n : ℕ => (n : ℝ) * R (b (m n) + y * a (m n))) atTop (𝓝 ((K : ℝ) * Real.exp (-y))) := by
    intro y hy
    have h1 := (hu y hy).comp hm_top
    have h2 := hratio.mul h1
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop K] with n hn
    have hq1 : 1 ≤ n / K := (Nat.one_le_div_iff hKnat).2 hn
    have hqpos : (0 : ℝ) < ((m n : ℕ) : ℝ) := by exact_mod_cast hq1
    simp only [Function.comp]
    field_simp
  have hn0 : ∀ n : ℕ, (0 : ℝ) ≤ n := fun n => Nat.cast_nonneg n
  -- comparison: for x > 0, y > 0 with x > y - L, eventually b_m + y a_m < b_n + x a_n
  have cmp1 : ∀ x y : ℝ, 0 < x → 0 < y → y - L < x →
      ∀ᶠ n in atTop, b (m n) + y * a (m n) < b n + x * a n := by
    intro x y hx hy hxy
    refine eventually_lt_of_antitone hR (fun n => (n : ℝ)) hn0 _ _ _ _ (hu x hx) (hv y hy) ?_
    rw [← hexpL, ← Real.exp_add]
    exact Real.exp_lt_exp.2 (by linarith)
  have cmp2 : ∀ x y : ℝ, 0 < x → 0 < y → x < y - L →
      ∀ᶠ n in atTop, b n + x * a n < b (m n) + y * a (m n) := by
    intro x y hx hy hxy
    refine eventually_lt_of_antitone hR (fun n => (n : ℝ)) hn0 _ _ _ _ (hv y hy) (hu x hx) ?_
    rw [← hexpL, ← Real.exp_add]
    exact Real.exp_lt_exp.2 (by linarith)
  -- main squeeze
  set s := 1 - x₀ with hs
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  set y₀ := x₀ + L with hy₀
  have hy₀1 : 1 < y₀ := by rw [hy₀]; linarith
  have hlim : ∀ ε' : ℝ, (K : ℝ) * Real.exp (-(y₀ + ε')) = Real.exp (-x₀) * Real.exp (-ε') := by
    intro ε'
    rw [← hexpL, ← Real.exp_add, ← Real.exp_add, hy₀]
    congr 1
    ring
  refine tendsto_of_exp_squeeze _ _ (Real.exp_pos _) ?_
  intro ε' hε'0 hε'1
  set ε := ε' / (1 + 2 * s) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεlt : ε < 1 := by
    rw [hε, div_lt_one (by positivity)]
    linarith
  have hε' : ε' = ε * (1 + 2 * s) := by rw [hε]; field_simp
  refine ⟨fun n => (n : ℝ) * R (b (m n) + (y₀ + ε') * a (m n)),
    fun n => (n : ℝ) * R (b (m n) + (y₀ - ε') * a (m n)), ?_, ?_, ?_⟩
  · rw [← hlim]
    exact hv _ (by linarith)
  · have := hv (y₀ - ε') (by linarith)
    rw [show y₀ - ε' = y₀ + (-ε') by ring, hlim, neg_neg] at this
    exact this
  · have c1 := cmp1 1 (1 + L - ε) one_pos (by linarith) (by linarith)
    have c2 := cmp2 1 (1 + L + ε) one_pos (by linarith) (by linarith)
    have c3 := cmp2 2 (2 + L + ε) two_pos (by linarith) (by linarith)
    have c4 := cmp1 2 (2 + L - ε) two_pos (by linarith) (by linarith)
    filter_upwards [c1, c2, c3, c4] with n h1 h2 h3 h4
    have ham := ha (m n)
    have han := ha n
    have hspos : 0 < s := by linarith
    -- a_n < (1 + 2ε) a_m and a_n > (1 - 2ε) a_m
    have hA1 : a n < (1 + 2 * ε) * a (m n) := by linarith
    have hA2 : (1 - 2 * ε) * a (m n) < a n := by linarith
    have hA1' := mul_lt_mul_of_pos_left hA1 hspos
    have hA2' := mul_lt_mul_of_pos_left hA2 hspos
    have hx₀ : x₀ = 1 - s := by rw [hs]; ring
    have hP1 : b (m n) + (y₀ - ε') * a (m n) < b n + x₀ * a n := by
      rw [hx₀, hε', hy₀, hs]
      nlinarith
    have hP2 : b n + x₀ * a n < b (m n) + (y₀ + ε') * a (m n) := by
      rw [hx₀, hε', hy₀, hs]
      nlinarith
    constructor
    · exact mul_le_mul_of_nonneg_left (hR hP2.le) (hn0 n)
    · exact mul_le_mul_of_nonneg_left (hR hP1.le) (hn0 n)

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


theorem theorem_3_core (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    InDr μ piLaw ↔ InD μ lambdaLaw ∧ InDZero μ := by
  constructor
  · intro h
    refine ⟨?_, h.1⟩
    obtain ⟨a, b, ha, hT⟩ := equation_11_positive_core μ h
    have hT' := equation_11_all_core μ a b ha hT
    exact ⟨a, b, ha, (gnedenko_core μ a b ha).2 hT'⟩
  · rintro ⟨hmax, hpos⟩
    exact max_to_residual_core μ hmax hpos

end BalkemaDeHaan.ExpDomain

open BalkemaDeHaan.ExpDomain
open MeasureTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    InDr μ piLaw ↔ InD μ lambdaLaw ∧ InDZero μ := by
  exact theorem_3_core μ
