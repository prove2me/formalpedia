-- Prove2me | solution 1 for DistTransform.Distortion.chambers_quantile
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:57:40.585268+00:00
-- url     : https://prove2.me/submissions/43f92b65-d83a-46fe-bc0f-9589edc90f3c

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

namespace Aux_DTDch
open DistTransform.Distortion

noncomputable def clamp (c : ℝ) : ℝ := max 0 (min c 1)

lemma clamp_nonneg (c : ℝ) : 0 ≤ clamp c := le_max_left _ _
lemma clamp_le_one (c : ℝ) : clamp c ≤ 1 := max_le zero_le_one (min_le_right _ _)
lemma clamp_of_mem {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : clamp c = c := by
  unfold clamp; rw [min_eq_left h1, max_eq_right h0]
lemma continuous_clamp : Continuous clamp :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The two-point distribution with mass `c` at `0` and `1 - c` at `1`
(a scaled Bernoulli law), for `c ∈ [0, 1]`. -/
noncomputable def twoPtM (c : ℝ) : Measure ℝ :=
  ENNReal.ofReal (clamp c) • Measure.dirac 0 + ENNReal.ofReal (1 - clamp c) • Measure.dirac 1

instance (c : ℝ) : IsProbabilityMeasure (twoPtM c) := by
  constructor
  simp only [twoPtM, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (clamp_nonneg c) (by linarith [clamp_le_one c])]
  simp

noncomputable def twoPt (c : ℝ) : ProbabilityMeasure ℝ := ⟨twoPtM c, inferInstance⟩

lemma cdf_twoPt (c x : ℝ) :
    cdf (twoPt c : Measure ℝ) x =
      (if 0 ≤ x then clamp c else 0) + (if 1 ≤ x then 1 - clamp c else 0) := by
  rw [cdf_eq_real, measureReal_def]
  show (twoPtM c (Set.Iic x)).toReal = _
  simp only [twoPtM, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Iic, Set.indicator, Set.mem_Iic, Pi.one_apply]
  have h1 := clamp_nonneg c
  have h2 := clamp_le_one c
  split_ifs <;> simp [ENNReal.toReal_add, ENNReal.ofReal_ne_top, h1, h2] <;> linarith

lemma cdf_twoPt_neg (c x : ℝ) (hx : x < 0) : cdf (twoPt c : Measure ℝ) x = 0 := by
  rw [cdf_twoPt, if_neg (by linarith), if_neg (by linarith)]; simp

lemma cdf_twoPt_mid (c x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    cdf (twoPt c : Measure ℝ) x = clamp c := by
  rw [cdf_twoPt, if_pos hx0, if_neg (by linarith)]; simp

lemma cdf_twoPt_ge (c x : ℝ) (hx : 1 ≤ x) : cdf (twoPt c : Measure ℝ) x = 1 := by
  rw [cdf_twoPt, if_pos (by linarith), if_pos hx]; ring

lemma twoPt_mem_Minf (c : ℝ) : twoPt c ∈ Minf := by
  refine ⟨0, 1, ?_⟩
  show twoPtM c (Set.Icc 0 1) = 1
  simp only [twoPtM, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Icc, Set.indicator, Set.mem_Icc, Pi.one_apply]
  simp only [le_refl, zero_le_one, and_self, if_true, mul_one]
  rw [← ENNReal.ofReal_add (clamp_nonneg c) (by linarith [clamp_le_one c])]
  simp

lemma integral_twoPt (c : ℝ) (f : ℝ →ᵇ ℝ) :
    ∫ ω, f ω ∂(twoPt c : Measure ℝ) = clamp c * f 0 + (1 - clamp c) * f 1 := by
  show ∫ ω, f ω ∂(twoPtM c) = _
  have h1 := clamp_nonneg c
  have h2 : 0 ≤ 1 - clamp c := by linarith [clamp_le_one c]
  unfold twoPtM
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2, smul_eq_mul, smul_eq_mul]
  · exact (f.integrable _).smul_measure ENNReal.ofReal_ne_top
  · exact (f.integrable _).smul_measure ENNReal.ofReal_ne_top

lemma tendsto_twoPt {cs : ℕ → ℝ} {c : ℝ} (h : Tendsto cs atTop (𝓝 c)) :
    Tendsto (fun n => twoPt (cs n)) atTop (𝓝 (twoPt c)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp only [integral_twoPt]
  have hc : Tendsto (fun n => clamp (cs n)) atTop (𝓝 (clamp c)) :=
    (continuous_clamp.tendsto c).comp h
  exact (hc.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub hc).mul tendsto_const_nhds)


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

/-- Least-element description of the left quantile at a level `u ∈ (0,1]` with a nonempty
upper set. -/
lemma lq_isLeast' (F : ProbabilityMeasure ℝ) {u : ℝ} (hu0 : 0 < u)
    (hne : {x : ℝ | u ≤ cdf (F : Measure ℝ) x}.Nonempty) :
    IsLeast {x : ℝ | u ≤ cdf (F : Measure ℝ) x} (leftQuantile F u) := by
  refine ⟨?_, fun x hx => csInf_le (qset_bdd F hu0) hx⟩
  show u ≤ cdf (F : Measure ℝ) (sInf {y : ℝ | u ≤ cdf (F : Measure ℝ) y})
  rw [← (cdf (F : Measure ℝ)).iInf_Ioi_eq]
  apply le_ciInf
  intro r
  obtain ⟨y, hyS, hyr⟩ := exists_lt_of_csInf_lt hne r.2
  exact hyS.trans (monotone_cdf _ hyr.le)


lemma cdf_shape (φ : ℝ ≃o ℝ) (F : ProbabilityMeasure ℝ) (x : ℝ) :
    cdf (shape φ F : Measure ℝ) x = cdf (F : Measure ℝ) (φ.symm x) := by
  rw [cdf_eq_real, cdf_eq_real, shape, ProbabilityMeasure.toMeasure_map,
    measureReal_def, measureReal_def, Measure.map_apply φ.continuous.measurable measurableSet_Iic,
    OrderIso.preimage_Iic]

lemma pm_ext (μ ν : ProbabilityMeasure ℝ)
    (h : ∀ x, cdf (μ : Measure ℝ) x = cdf (ν : Measure ℝ) x) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.eq_of_cdf _ _ (StieltjesFunction.ext h)

/-- cdf of the image of the two-point law under an order isomorphism `φ`. -/
lemma cdf_shape_twoPt (φ : ℝ ≃o ℝ) (c z : ℝ) :
    cdf (shape φ (twoPt c) : Measure ℝ) z =
      (if φ 0 ≤ z then clamp c else 0) + (if φ 1 ≤ z then 1 - clamp c else 0) := by
  rw [cdf_shape, cdf_twoPt]
  simp only [OrderIso.le_symm_apply]

/-- The affine order isomorphism `x ↦ s + (t - s) x` (`s < t`), sending `0 ↦ s`, `1 ↦ t`. -/
noncomputable def aff (s t : ℝ) (hst : s < t) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun x => s + (t - s) * x)
    (fun x y hxy => by have : 0 < t - s := by linarith
                       nlinarith)
    (fun y => ⟨(y - s) / (t - s), by
      have : t - s ≠ 0 := by linarith
      field_simp; ring⟩)

lemma aff_apply (s t : ℝ) (hst : s < t) (x : ℝ) : aff s t hst x = s + (t - s) * x := rfl

/-- An order isomorphism fixing `0` and `1`: the identity off `[0,1]` and `x ↦ x²` on it. -/
noncomputable def sqFun (x : ℝ) : ℝ := if x ≤ 0 then x else if x ≤ 1 then x ^ 2 else x

lemma sqFun_strictMono : StrictMono sqFun := by
  intro x y hxy
  unfold sqFun
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> nlinarith

lemma sqFun_surj : Function.Surjective sqFun := by
  intro y
  by_cases h0 : y ≤ 0
  · exact ⟨y, by simp [sqFun, h0]⟩
  by_cases h1 : y ≤ 1
  · push Not at h0
    refine ⟨Real.sqrt y, ?_⟩
    have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.2 h0
    have hs1 : Real.sqrt y ≤ 1 := Real.sqrt_le_one.mpr h1
    simp only [sqFun, if_neg (not_le.2 hs0), if_pos hs1]
    exact Real.sq_sqrt h0.le
  · push Not at h0 h1
    exact ⟨y, by simp [sqFun, not_le.2 h0, not_le.2 h1]⟩

noncomputable def sqIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective sqFun sqFun_strictMono sqFun_surj

lemma sqIso_apply (x : ℝ) : sqIso x = sqFun x := rfl

lemma shape_mem_Minf (φ : ℝ ≃o ℝ) (F : ProbabilityMeasure ℝ) (hF : F ∈ Minf) :
    shape φ F ∈ Minf := by
  obtain ⟨a, b, hab⟩ := hF
  refine ⟨φ a, φ b, ?_⟩
  rw [shape, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply φ.continuous.measurable measurableSet_Icc, OrderIso.preimage_Icc]
  simpa using hab

end Aux_DTDch

open DistTransform.Distortion Aux_DTDch in
theorem solution (q : ProbabilityMeasure ℝ → ℝ)
    (hq_mono : ∀ F ∈ Minf, ∀ G ∈ Minf, StLE F G → q F ≤ q G)
    (hq_shape : ∀ φ : ℝ ≃o ℝ, ∀ F ∈ Minf, q (shape φ F) = φ (q F)) :
    ∃ α ∈ Set.Icc (0 : ℝ) 1,
      (0 < α ∧ ∀ F ∈ Minf, q F = leftQuantile F α) ∨
        (α < 1 ∧ ∀ F ∈ Minf, q F = rightQuantile F α) := by
  have hB := twoPt_mem_Minf
  -- `v c = q(B_c)` for the two-point law `B_c = c δ₀ + (1-c) δ₁`
  -- (1) `q(δ₀) = 0` and `q(δ₁) = 1`
  have hv1 : q (twoPt 1) = 0 := by
    have hs : shape (aff 0 2 (by norm_num)) (twoPt 1) = twoPt 1 := by
      apply pm_ext; intro z
      rw [cdf_shape_twoPt, cdf_twoPt, aff_apply, aff_apply, clamp_of_mem zero_le_one le_rfl]
      norm_num
    have := hq_shape (aff 0 2 (by norm_num)) _ (hB 1)
    rw [hs, aff_apply] at this
    linarith
  have hv0 : q (twoPt 0) = 1 := by
    have hs : shape (aff (-1) 1 (by norm_num)) (twoPt 0) = twoPt 0 := by
      apply pm_ext; intro z
      rw [cdf_shape_twoPt, cdf_twoPt, aff_apply, aff_apply, clamp_of_mem le_rfl zero_le_one]
      norm_num
    have := hq_shape (aff (-1) 1 (by norm_num)) _ (hB 0)
    rw [hs, aff_apply] at this
    linarith
  -- (2) monotonicity of `c ↦ q(B_c)` (decreasing)
  have hvmono : ∀ c c', c ≤ c' → q (twoPt c') ≤ q (twoPt c) := by
    intro c c' hcc
    apply hq_mono _ (hB _) _ (hB _)
    rw [stLE_iff]
    intro z
    rw [cdf_twoPt, cdf_twoPt]
    have hcl : clamp c ≤ clamp c' := max_le_max le_rfl (min_le_min hcc le_rfl)
    have := clamp_nonneg c
    have := clamp_le_one c'
    split_ifs <;> linarith
  -- (3) `q(B_c) ∈ {0, 1}` for `c ∈ [0,1]`, by covariance under a map fixing `0` and `1`
  have hv01 : ∀ c ∈ Set.Icc (0:ℝ) 1, q (twoPt c) = 0 ∨ q (twoPt c) = 1 := by
    intro c hc
    have hlo : 0 ≤ q (twoPt c) := hv1 ▸ hvmono c 1 hc.2
    have hhi : q (twoPt c) ≤ 1 := hv0 ▸ hvmono 0 c hc.1
    have hs : shape sqIso (twoPt c) = twoPt c := by
      apply pm_ext; intro z
      rw [cdf_shape_twoPt, cdf_twoPt, sqIso_apply, sqIso_apply]
      simp [sqFun]
    have := hq_shape sqIso _ (hB c)
    rw [hs, sqIso_apply] at this
    by_contra hne
    push Not at hne
    have h0 : 0 < q (twoPt c) := lt_of_le_of_ne hlo (Ne.symm hne.1)
    have h1 : q (twoPt c) < 1 := lt_of_le_of_ne hhi hne.2
    simp only [sqFun, if_neg (not_le.2 h0), if_pos h1.le] at this
    nlinarith
  have hv_nonneg : ∀ c ∈ Set.Icc (0:ℝ) 1, 0 ≤ q (twoPt c) := by
    intro c hc; rcases hv01 c hc with h | h <;> rw [h]; norm_num
  have cdf_mem : ∀ (F : ProbabilityMeasure ℝ) x, cdf (F : Measure ℝ) x ∈ Set.Icc (0:ℝ) 1 :=
    fun F x => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  -- support bounds for `F ∈ M∞`
  have hFb : ∀ F ∈ Minf, ∃ a b : ℝ, (∀ z, z < a → cdf (F : Measure ℝ) z = 0) ∧
      (∀ z, b ≤ z → cdf (F : Measure ℝ) z = 1) := by
    rintro F ⟨a, b, hab⟩
    refine ⟨a, b, fun z hz => ?_, fun z hz => ?_⟩
    · apply le_antisymm _ (cdf_nonneg _ _)
      rw [cdf_eq_real, measureReal_def]
      have h0 : (F : Measure ℝ) (Set.Iic z) = 0 := by
        have hc : (F : Measure ℝ) (Set.Icc a b)ᶜ = 0 := by
          rw [prob_compl_eq_one_sub measurableSet_Icc, hab, tsub_self]
        apply measure_mono_null _ hc
        intro y hy
        simp only [Set.mem_Iic] at hy
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
        intro hay; linarith
      rw [h0]; simp
    · apply le_antisymm (cdf_le_one _ _)
      rw [cdf_eq_real, measureReal_def]
      have h1 : (F : Measure ℝ) (Set.Iic z) = 1 := by
        apply le_antisymm prob_le_one
        rw [← hab]
        apply measure_mono
        intro y hy; exact Set.mem_Iic.2 (hy.2.trans hz)
      rw [h1]; simp
  -- (4) comparison with two-point laws
  have hup : ∀ F ∈ Minf, ∀ x, q (twoPt (cdf (F : Measure ℝ) x)) = 0 → q F ≤ x := by
    intro F hF x hx
    obtain ⟨a, b, ha, hb⟩ := hFb F hF
    set t := max x b + 1 with ht
    have hxt : x < t := by linarith [le_max_left x b]
    set c := cdf (F : Measure ℝ) x with hc
    have hcl : clamp c = c := clamp_of_mem (cdf_mem F x).1 (cdf_mem F x).2
    have hle : StLE F (shape (aff x t hxt) (twoPt c)) := by
      rw [stLE_iff]
      intro z
      rw [cdf_shape_twoPt, aff_apply, aff_apply, hcl]
      simp only [mul_zero, add_zero, mul_one, add_sub_cancel]
      split_ifs with h1 h2 h2
      · rw [hb z (by linarith [le_max_right x b])]; ring_nf; exact le_rfl
      · simp only [add_zero]; exact monotone_cdf _ h1
      · linarith
      · simp only [add_zero]; exact cdf_nonneg _ _
    have h1 := hq_mono F hF _ (shape_mem_Minf _ _ (hB c)) hle
    rw [hq_shape _ _ (hB c), aff_apply, hx] at h1
    linarith
  have hdown : ∀ F ∈ Minf, ∀ x, q (twoPt (cdf (F : Measure ℝ) x)) = 1 → x ≤ q F := by
    intro F hF x hx
    obtain ⟨a, b, ha, hb⟩ := hFb F hF
    set s := min a x - 1 with hs
    have hsx : s < x := by linarith [min_le_right a x]
    have hsa : s < a := by linarith [min_le_left a x]
    set c := cdf (F : Measure ℝ) x with hc
    have hcl : clamp c = c := clamp_of_mem (cdf_mem F x).1 (cdf_mem F x).2
    have hle : StLE (shape (aff s x hsx) (twoPt c)) F := by
      rw [stLE_iff]
      intro z
      rw [cdf_shape_twoPt, aff_apply, aff_apply, hcl]
      simp only [mul_zero, add_zero, mul_one, add_sub_cancel]
      split_ifs with h1 h2 h2
      · ring_nf; exact cdf_le_one _ _
      · simp only [add_zero]; exact monotone_cdf _ (by linarith)
      · linarith
      · simp only [add_zero]; rw [ha z (by linarith)]
    have h1 := hq_mono _ (shape_mem_Minf _ _ (hB c)) F hF hle
    rw [hq_shape _ _ (hB c), aff_apply, hx] at h1
    linarith
  -- (5) the threshold level `α`
  set S := {c : ℝ | c ∈ Set.Icc (0:ℝ) 1 ∧ q (twoPt c) = 0} with hS
  have hSne : S.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, hv1⟩
  have hSbdd : BddBelow S := ⟨0, fun c hc => hc.1.1⟩
  set α := sInf S with hα
  have hα0 : 0 ≤ α := le_csInf hSne (fun c hc => hc.1.1)
  have hα1 : α ≤ 1 := csInf_le hSbdd ⟨⟨zero_le_one, le_rfl⟩, hv1⟩
  -- a level `c` with `q(B_c) ≠ 0` is at most `α`
  have hnot : ∀ c ∈ Set.Icc (0:ℝ) 1, q (twoPt c) ≠ 0 → q (twoPt c) = 1 := by
    intro c hc hne; rcases hv01 c hc with h | h
    · exact absurd h hne
    · exact h
  refine ⟨α, ⟨hα0, hα1⟩, ?_⟩
  by_cases hαS : α ∈ S
  · -- left quantile case
    have hαpos : 0 < α := by
      rcases eq_or_lt_of_le hα0 with h | h
      · exfalso; have := hαS.2; rw [← h, hv0] at this; norm_num at this
      · exact h
    refine Or.inl ⟨hαpos, fun F hF => ?_⟩
    obtain ⟨a, b, ha, hb⟩ := hFb F hF
    have hne : {x : ℝ | α ≤ cdf (F : Measure ℝ) x}.Nonempty :=
      ⟨b, by simp only [Set.mem_setOf_eq, hb b le_rfl]; exact hα1⟩
    have hl := lq_isLeast' F hαpos hne
    set m := leftQuantile F α
    apply le_antisymm
    · apply hup F hF m
      apply le_antisymm _ (hv_nonneg _ (cdf_mem F m))
      rw [← hαS.2]; exact hvmono _ _ hl.1
    · by_contra hlt
      push Not at hlt
      set x := (q F + m) / 2
      have hxm : x < m := by simp only [x]; linarith
      have hFx : cdf (F : Measure ℝ) x < α := by
        by_contra hge; push Not at hge; exact absurd (hl.2 hge) (not_le.2 hxm)
      have hv : q (twoPt (cdf (F : Measure ℝ) x)) = 1 := by
        apply hnot _ (cdf_mem F x)
        intro h0
        exact absurd (csInf_le hSbdd ⟨cdf_mem F x, h0⟩) (not_le.2 hFx)
      have := hdown F hF x hv
      simp only [x] at this; linarith
  · -- right quantile case
    have hαlt1 : α < 1 := by
      rcases eq_or_lt_of_le hα1 with h | h
      · exfalso; apply hαS; rw [h]; exact ⟨⟨zero_le_one, le_rfl⟩, hv1⟩
      · exact h
    refine Or.inr ⟨hαlt1, fun F hF => ?_⟩
    obtain ⟨a, b, ha, hb⟩ := hFb F hF
    have hne : {x : ℝ | α < cdf (F : Measure ℝ) x}.Nonempty :=
      ⟨b, by simp only [Set.mem_setOf_eq, hb b le_rfl]; exact hαlt1⟩
    have hbdd : BddBelow {x : ℝ | α < cdf (F : Measure ℝ) x} := by
      refine ⟨a, fun x hx => ?_⟩
      by_contra hxa; push Not at hxa
      have : α < cdf (F : Measure ℝ) x := hx
      rw [ha x hxa] at this; linarith
    set m := rightQuantile F α with hm
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      set x := (q F + m) / 2
      have hxm : m < x := by simp only [x]; linarith
      obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne hxm
      have hFx : α < cdf (F : Measure ℝ) x := lt_of_lt_of_le hy (monotone_cdf _ hyx.le)
      obtain ⟨c', hc'S, hc'x⟩ := exists_lt_of_csInf_lt hSne hFx
      have hv : q (twoPt (cdf (F : Measure ℝ) x)) = 0 := by
        apply le_antisymm _ (hv_nonneg _ (cdf_mem F x))
        rw [← hc'S.2]; exact hvmono _ _ hc'x.le
      have := hup F hF x hv
      simp only [x] at this; linarith
    · by_contra hlt
      push Not at hlt
      set x := (q F + m) / 2
      have hxm : x < m := by simp only [x]; linarith
      have hFx : cdf (F : Measure ℝ) x ≤ α := by
        by_contra hge; push Not at hge; exact absurd (csInf_le hbdd hge) (not_le.2 hxm)
      have hv : q (twoPt (cdf (F : Measure ℝ) x)) = 1 := by
        apply hnot _ (cdf_mem F x)
        intro h0
        have hαle : α ≤ cdf (F : Measure ℝ) x := csInf_le hSbdd ⟨cdf_mem F x, h0⟩
        apply hαS
        rw [← le_antisymm hFx hαle]
        exact ⟨cdf_mem F x, h0⟩
      have := hdown F hF x hv
      simp only [x] at this; linarith
