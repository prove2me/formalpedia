-- Prove2me | solution 1 for DistTransform.Distortion.mplus_case
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:52:23.161442+00:00
-- url     : https://prove2.me/submissions/aa5f15de-cab8-44d9-826e-2db508b71c86

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model
import Theorems.Thm_DistTransform_Distortion_remark_p4

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

namespace Aux_DTDmp
open DistTransform.Distortion

lemma ioi_eq (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    (μ : Measure ℝ) {ω | x < id ω} = ENNReal.ofReal (1 - cdf (μ : Measure ℝ) x) := by
  have h1 : {ω : ℝ | x < id ω} = (Set.Iic x)ᶜ := by ext; simp
  rw [h1, prob_compl_eq_one_sub measurableSet_Iic, cdf_eq_real, measureReal_def,
    ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal
      (measure_ne_top _ _)]

lemma stLE_iff (F G : ProbabilityMeasure ℝ) :
    StLE F G ↔ ∀ x, cdf (G : Measure ℝ) x ≤ cdf (F : Measure ℝ) x := by
  unfold StLE StochasticOrders.Usual.UsualOrder
  refine forall_congr' fun x => ?_
  rw [ioi_eq, ioi_eq, ENNReal.ofReal_le_ofReal_iff]
  · constructor <;> intro h <;> linarith
  · linarith [cdf_le_one (G : Measure ℝ) x]

lemma qset_nonempty (F : ProbabilityMeasure ℝ) {p : ℝ} (hp1 : p < 1) :
    {x : ℝ | p ≤ cdf (F : Measure ℝ) x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop (μ := (F : Measure ℝ))).eventually
    (lt_mem_nhds hp1)).exists
  exact ⟨x, hx.le⟩

lemma qset_bdd (F : ProbabilityMeasure ℝ) {p : ℝ} (hp0 : 0 < p) :
    BddBelow {x : ℝ | p ≤ cdf (F : Measure ℝ) x} := by
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 ((tendsto_cdf_atBot (μ := (F : Measure ℝ))).eventually
    (gt_mem_nhds hp0))
  refine ⟨a, fun x hx => ?_⟩
  by_contra hxa
  push Not at hxa
  have := ha x hxa.le
  simp only [Set.mem_setOf_eq] at hx
  linarith

lemma leftQuantile_mono {F G : ProbabilityMeasure ℝ}
    (h : ∀ x, cdf (G : Measure ℝ) x ≤ cdf (F : Measure ℝ) x) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : leftQuantile F p ≤ leftQuantile G p := by
  unfold leftQuantile
  exact csInf_le_csInf (qset_bdd F hp0) (qset_nonempty G hp1)
    (fun x hx => le_trans hx (h x))

/-- The left quantile at level `u ∈ (0,1)` is the least point of `{x : u ≤ F(x)}`. -/
lemma leftQuantile_isLeast (F : ProbabilityMeasure ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    IsLeast {x : ℝ | u ≤ cdf (F : Measure ℝ) x} (leftQuantile F u) := by
  have hne := qset_nonempty F hu1
  refine ⟨?_, fun x hx => csInf_le (qset_bdd F hu0) hx⟩
  show u ≤ cdf (F : Measure ℝ) (sInf {y : ℝ | u ≤ cdf (F : Measure ℝ) y})
  rw [← (cdf (F : Measure ℝ)).iInf_Ioi_eq]
  apply le_ciInf
  intro r
  obtain ⟨y, hyS, hyr⟩ := exists_lt_of_csInf_lt hne r.2
  exact hyS.trans (monotone_cdf _ hyr.le)

lemma cdf_map (F : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (hf : Measurable f) (x : ℝ) :
    cdf ((F.map hf.aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) x =
      (F : Measure ℝ).real (f ⁻¹' Set.Iic x) := by
  rw [cdf_eq_real, ProbabilityMeasure.toMeasure_map, measureReal_def, measureReal_def,
    Measure.map_apply hf measurableSet_Iic]

/-- A distribution with `F(a) = 0` and `F(b) = 1` lies in `M∞`. -/
lemma mem_Minf_of (G : ProbabilityMeasure ℝ) (a b : ℝ) (ha : cdf (G : Measure ℝ) a = 0)
    (hb : cdf (G : Measure ℝ) b = 1) : G ∈ Minf := by
  have hab : a ≤ b := by
    by_contra hlt
    push Not at hlt
    have := monotone_cdf (G : Measure ℝ) hlt.le
    linarith
  refine ⟨a, b, ?_⟩
  apply le_antisymm prob_le_one
  have hIoc : (G : Measure ℝ).real (Set.Ioc a b) = 1 := by
    have hset : Set.Ioc a b = Set.Iic b \ Set.Iic a := by
      ext z; simp only [Set.mem_Ioc, Set.mem_diff, Set.mem_Iic, not_le]; tauto
    rw [hset, measureReal_diff (Set.Iic_subset_Iic.2 hab) measurableSet_Iic]
    rw [cdf_eq_real] at ha hb
    rw [ha, hb]; norm_num
  have h1 : (G : Measure ℝ) (Set.Ioc a b) = 1 := by
    rw [measureReal_def] at hIoc
    have := (ENNReal.toReal_eq_one_iff _).1 hIoc
    exact this
  calc (1 : ENNReal) = (G : Measure ℝ) (Set.Ioc a b) := h1.symm
    _ ≤ (G : Measure ℝ) (Set.Icc a b) := measure_mono Set.Ioc_subset_Icc_self


lemma galois (F : ProbabilityMeasure ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (x : ℝ) :
    leftQuantile F u ≤ x ↔ u ≤ cdf (F : Measure ℝ) x := by
  constructor
  · intro hq
    exact (leftQuantile_isLeast F hu0 hu1).1.trans (monotone_cdf _ hq)
  · intro hx
    exact (leftQuantile_isLeast F hu0 hu1).2 hx

lemma leftQuantile_level_mono (F : ProbabilityMeasure ℝ) {p p' : ℝ} (hp0 : 0 < p)
    (hpp : p ≤ p') (hp'1 : p' < 1) : leftQuantile F p ≤ leftQuantile F p' := by
  unfold leftQuantile
  exact csInf_le_csInf (qset_bdd F hp0) (qset_nonempty F hp'1)
    (fun x hx => le_trans hpp hx)

lemma unif_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | p ≤ c} = c := by
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Ioo]
  have h1 : volume ({p : ℝ | p ≤ c} ∩ Set.Ioo 0 1) = ENNReal.ofReal c := by
    apply le_antisymm
    · calc volume ({p : ℝ | p ≤ c} ∩ Set.Ioo 0 1) ≤ volume (Set.Ioc (0:ℝ) c) := by
            apply measure_mono
            rintro p ⟨hp, hp0, _⟩
            exact ⟨hp0, hp⟩
        _ = ENNReal.ofReal c := by rw [Real.volume_Ioc]; simp
    · calc ENNReal.ofReal c = volume (Set.Ioo (0:ℝ) c) := by rw [Real.volume_Ioo]; simp
        _ ≤ volume ({p : ℝ | p ≤ c} ∩ Set.Ioo 0 1) := by
            apply measure_mono
            rintro p ⟨hp0, hp⟩
            exact ⟨le_of_lt hp, hp0, lt_of_lt_of_le hp hc1⟩
  rw [h1, ENNReal.toReal_ofReal hc0]

lemma cdf_eq_unif_quantile (G : ProbabilityMeasure ℝ) (x : ℝ) :
    cdf (G : Measure ℝ) x =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | leftQuantile G p ≤ x} := by
  have hr := (remark_p4 id (monotoneOn_id) (fun p hp => ⟨hp.1, hp.2.le⟩)).2.2
    (fun p hp => hp.2) G x
  simp only [id] at hr
  rw [hr, unif_le _ (cdf_nonneg _ _) (cdf_le_one _ _)]

lemma restrict_mono_Ioo (S S' : Set ℝ) (h : ∀ p ∈ Set.Ioo (0:ℝ) 1, p ∈ S → p ∈ S') :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).real S ≤
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).real S' := by
  rw [measureReal_def, measureReal_def, Measure.restrict_apply' measurableSet_Ioo,
    Measure.restrict_apply' measurableSet_Ioo]
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top (b := volume (Set.Ioo (0:ℝ) 1))
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (measure_mono Set.inter_subset_right)
  · apply measure_mono
    rintro p ⟨hp, hp'⟩
    exact ⟨h p hp' hp, hp'⟩

instance unif_prob : IsProbabilityMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; simp⟩

/-- `law(f_n(X)) → law(f(X))` weakly when `f_n → f` pointwise (dominated convergence). -/
lemma tendsto_map_of_pointwise (F : ProbabilityMeasure ℝ) (fs : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfs : ∀ n, Measurable (fs n)) (hf : Measurable f)
    (hlim : ∀ y, Tendsto (fun n => fs n y) atTop (𝓝 (f y))) (hfc : ∀ n, Continuous (fs n))
    (hfc' : Continuous f) :
    Tendsto (fun n => F.map (hfs n).aemeasurable) atTop (𝓝 (F.map hf.aemeasurable)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map hf.aemeasurable g.continuous.aestronglyMeasurable]
  simp_rw [integral_map (hfs _).aemeasurable g.continuous.aestronglyMeasurable]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖) (fun n => ?_)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun y => g.norm_coe_le_norm _)
    (Filter.Eventually.of_forall fun y => ?_)
  · exact (g.continuous.comp (hfc n)).aestronglyMeasurable
  · exact (g.continuous.tendsto _).comp (hlim y)

end Aux_DTDmp

namespace Aux_DTDmp
open DistTransform.Distortion

lemma meas_min (n : ℝ) : Measurable (fun y : ℝ => min y n) := measurable_id.min measurable_const

lemma cdf_min_lt (F : ProbabilityMeasure ℝ) (n y : ℝ) (hy : y < n) :
    cdf ((F.map (meas_min n).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) y =
      cdf (F : Measure ℝ) y := by
  rw [cdf_map _ _ (meas_min n), cdf_eq_real]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic, min_le_iff]
  constructor
  · rintro (h | h)
    · exact h
    · linarith
  · intro h; exact Or.inl h

lemma cdf_min_ge (F : ProbabilityMeasure ℝ) (n y : ℝ) (hy : n ≤ y) :
    cdf ((F.map (meas_min n).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) y = 1 := by
  rw [cdf_map _ _ (meas_min n)]
  have : (fun z : ℝ => min z n) ⁻¹' Set.Iic y = Set.univ := by
    ext z; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
    exact (min_le_right z n).trans hy
  rw [this, probReal_univ]

lemma cdf_le_min (F : ProbabilityMeasure ℝ) (n y : ℝ) :
    cdf (F : Measure ℝ) y ≤
      cdf ((F.map (meas_min n).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) y := by
  rw [cdf_map _ _ (meas_min n), cdf_eq_real]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz
  simp only [Set.mem_preimage, Set.mem_Iic] at hz ⊢
  exact (min_le_left z n).trans hz

/-- If `x₀ = F⁻¹(u) < n`, truncating `F` at `n` does not change the `u`-quantile. -/
lemma lq_min (F : ProbabilityMeasure ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (n : ℝ)
    (hn : leftQuantile F u < n) :
    leftQuantile (F.map (meas_min n).aemeasurable) u = leftQuantile F u := by
  have hl := leftQuantile_isLeast F hu0 hu1
  apply IsLeast.csInf_eq
  refine ⟨le_trans hl.1 (cdf_le_min F n _), fun y hy => ?_⟩
  rcases lt_or_ge y n with hyn | hyn
  · have hy' : u ≤ cdf (F : Measure ℝ) y := by
      have : u ≤ cdf ((F.map (meas_min n).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) y :=
        hy
      rwa [cdf_min_lt F n y hyn] at this
    exact hl.2 hy'
  · linarith

lemma min_mem_Minf (F : ProbabilityMeasure ℝ) (a n : ℝ) (ha : cdf (F : Measure ℝ) a = 0) :
    (F.map (meas_min n).aemeasurable : ProbabilityMeasure ℝ) ∈ Minf := by
  apply mem_Minf_of _ (min a (n - 1)) n
  · rw [cdf_min_lt F n _ (lt_of_le_of_lt (min_le_right _ _) (by linarith))]
    apply le_antisymm _ (cdf_nonneg _ _)
    rw [← ha]; exact monotone_cdf _ (min_le_left _ _)
  · exact cdf_min_ge F n n le_rfl

end Aux_DTDmp

open DistTransform.Distortion Aux_DTDmp in
theorem solution (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (hlsc : IsLSC Set.univ T) (hmono : IsMonotoneT Set.univ T)
    (hcomm : CommutesWithShape Set.univ T)
    (h : ℝ → ℝ) (hh_mono : MonotoneOn h (Set.Ioo 0 1))
    (hh_range : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1)
    (h4 : ∀ F ∈ Minf, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p)) :
    (∀ p ∈ Set.Ioo (0 : ℝ) 1, h p < 1) ∧
      ∀ F ∈ Mplus, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p) := by
  have qmono : ∀ F G : ProbabilityMeasure ℝ, (∀ x, cdf (G : Measure ℝ) x ≤ cdf (F : Measure ℝ) x) →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p ≤ leftQuantile (T G) p := by
    intro F G hFG p hp
    exact leftQuantile_mono ((stLE_iff _ _).1 (hmono F trivial G trivial
      ((stLE_iff _ _).2 hFG))) hp.1 hp.2
  -- Step (a): `h(p) < 1`, otherwise `q_p^T` would be infinite at an unbounded distribution.
  have hlt1 : ∀ p ∈ Set.Ioo (0 : ℝ) 1, h p < 1 := by
    intro p hp
    by_contra hge
    push Not at hge
    have h1 : h p = 1 := le_antisymm (hh_range p hp).2 hge
    let X : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
    have hX : ∀ x, cdf (X : Measure ℝ) x < 1 := by
      intro x
      have hpos : (X : Measure ℝ) (Set.Ioi x) ≠ 0 := by
        intro h0
        have := (gaussianReal_absolutelyContinuous' 0 one_ne_zero) h0
        rw [Real.volume_Ioi] at this
        exact ENNReal.top_ne_zero this
      have hc : (X : Measure ℝ) (Set.Iic x) = 1 - (X : Measure ℝ) (Set.Ioi x) := by
        rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi]
      rw [cdf_eq_real, measureReal_def, hc]
      have hlt : 1 - (X : Measure ℝ) (Set.Ioi x) < 1 :=
        ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos
      have hne : 1 - (X : Measure ℝ) (Set.Ioi x) ≠ ⊤ := ne_top_of_lt hlt
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_lt_toReal hne ENNReal.one_ne_top).2 hlt
    have mmax : Measurable (fun y : ℝ => max y 0) := measurable_id.max measurable_const
    set W := X.map mmax.aemeasurable with hW
    have hWcdf : ∀ x, cdf (W : Measure ℝ) x = if x < 0 then 0 else cdf (X : Measure ℝ) x := by
      intro x
      rw [hW, cdf_map _ _ mmax]
      split_ifs with hx
      · have : (fun y : ℝ => max y 0) ⁻¹' Set.Iic x = ∅ := by
          ext z; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
            not_le]
          exact lt_of_lt_of_le hx (le_max_right z 0)
        rw [this, measureReal_empty]
      · push Not at hx
        rw [cdf_eq_real]; congr 1; ext z
        simp only [Set.mem_preimage, Set.mem_Iic, max_le_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
    have hW0 : cdf (W : Measure ℝ) (-1) = 0 := by rw [hWcdf, if_pos (by norm_num)]
    have hWlt : ∀ x, cdf (W : Measure ℝ) x < 1 := by
      intro x; rw [hWcdf]; split_ifs
      · norm_num
      · exact hX x
    obtain ⟨n, hn⟩ := exists_nat_gt (leftQuantile (T W) p)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    set Fn := W.map (meas_min (n : ℝ)).aemeasurable with hFn
    have hFnM : Fn ∈ Minf := min_mem_Minf W (-1) n hW0
    have hqFn : leftQuantile Fn 1 = n := by
      apply IsLeast.csInf_eq
      refine ⟨?_, fun y hy => ?_⟩
      · show (1:ℝ) ≤ cdf _ (n : ℝ)
        rw [cdf_min_ge W n n le_rfl]
      · by_contra hyn
        push Not at hyn
        have : (1:ℝ) ≤ cdf (Fn : Measure ℝ) y := hy
        rw [cdf_min_lt W n y hyn] at this
        linarith [hWlt y]
    have e := h4 Fn hFnM p hp
    rw [h1, hqFn] at e
    have := qmono Fn W (cdf_le_min W n) p hp
    linarith
  refine ⟨hlt1, fun F hF p hp => ?_⟩
  obtain ⟨⟨a, ha⟩, _⟩ := hF
  have hu0 : 0 < h p := (hh_range p hp).1
  have hu1 : h p < 1 := hlt1 p hp
  set x0 := leftQuantile F (h p) with hx0
  apply le_antisymm
  · -- Step (c): upper bound by lower-semicontinuity, with `G = law(F⁻¹(h(U)))`.
    set μ := volume.restrict (Set.Ioo (0 : ℝ) 1) with hμ
    set Q : ℝ → ℝ := fun p' => leftQuantile F (h p') with hQ
    have hQmono : MonotoneOn Q (Set.Ioo 0 1) := by
      intro p₁ h₁ p₂ h₂ h12
      exact leftQuantile_level_mono F (hh_range p₁ h₁).1 (hh_mono h₁ h₂ h12) (hlt1 p₂ h₂)
    have hQm : AEMeasurable Q μ := aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hQmono
    let G : ProbabilityMeasure ℝ := ⟨μ.map Q, Measure.isProbabilityMeasure_map hQm⟩
    have hGcdf : ∀ x, cdf (G : Measure ℝ) x = μ.real {p' | Q p' ≤ x} := by
      intro x
      rw [cdf_eq_real, measureReal_def, measureReal_def]
      show ((μ.map Q) (Set.Iic x)).toReal = _
      rw [Measure.map_apply_of_aemeasurable hQm measurableSet_Iic]
      rfl
    have hlim := tendsto_map_of_pointwise F (fun n : ℕ => fun y => min y (n : ℝ)) id
      (fun n => meas_min n) measurable_id
      (fun y => tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop ⌈y⌉₊] with n hn
        have : y ≤ (n : ℝ) := (Nat.le_ceil y).trans (by exact_mod_cast hn)
        simp [min_eq_left this]))
      (fun n => continuous_id.min continuous_const) continuous_id
    have hFid : F.map measurable_id.aemeasurable = F := by
      apply ProbabilityMeasure.toMeasure_injective
      simp [ProbabilityMeasure.toMeasure_map, Measure.map_id]
    rw [hFid] at hlim
    have hle : ∀ n : ℕ, StLE (T (F.map (meas_min (n : ℝ)).aemeasurable)) G := by
      intro n
      rw [stLE_iff]
      intro x
      rw [hGcdf, cdf_eq_unif_quantile]
      apply restrict_mono_Ioo
      intro p' hp' hle'
      simp only [Set.mem_setOf_eq] at hle' ⊢
      rw [h4 _ (min_mem_Minf F a n ha) p' hp']
      refine le_trans ?_ hle'
      exact leftQuantile_mono (cdf_le_min F n) (hh_range p' hp').1 (hlt1 p' hp')
    have hTF := (stLE_iff _ _).1 (hlsc _ F G (fun _ => trivial) trivial trivial hlim hle)
    have h1 : leftQuantile (T F) p ≤ leftQuantile G p := leftQuantile_mono hTF hp.1 hp.2
    have h2 : leftQuantile G p ≤ Q p := by
      rw [galois G hp.1 hp.2, hGcdf]
      calc p = μ.real {p' | p' ≤ p} := (unif_le p hp.1.le hp.2.le).symm
        _ ≤ μ.real {p' | Q p' ≤ Q p} := by
          apply restrict_mono_Ioo
          intro p' hp' hpp
          exact hQmono hp' hp hpp
    exact h1.trans h2
  · -- Step (b), eq. (6): lower bound by monotonicity, truncating `F` at a large level `n`.
    obtain ⟨n, hn⟩ := exists_gt x0
    have e := h4 _ (min_mem_Minf F a n ha) p hp
    rw [lq_min F hu0 hu1 n hn] at e
    have := qmono _ F (cdf_le_min F n) p hp
    rw [e] at this
    exact this
