-- Prove2me | solution 1 for BalkemaDeHaan.ExpDomain.equation_11_positive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:45:42.079273+00:00
-- url     : https://prove2.me/submissions/104bb906-b5eb-447c-bc4e-f3cf45678ff8

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

end BalkemaDeHaan.ExpDomain

open BalkemaDeHaan.ExpDomain
open MeasureTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : InDr μ piLaw) :
    ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧
      TailScaledConvergence μ a b (Set.Ioi 0) := by
  exact equation_11_positive_core μ h
