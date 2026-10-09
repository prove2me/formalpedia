-- Prove2me | solution 1 for GaussianMatrix.entropy_tensorization
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:50:35.546686+00:00
-- url     : https://prove2.me/submissions/5cc7bb74-9d95-4bb3-8d0d-690ec699b451

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

set_option linter.unusedSectionVars false

namespace GaussianMatrix.EntTensor

/-- Pointwise Young/Gibbs inequality, scaled form. -/
lemma young_scaled {Z U m : ℝ} (hZ : 0 < Z) (hm : 0 < m) :
    Z * U ≤ Z * Real.log Z - Z * Real.log m - Z + m * Real.exp U := by
  have h1 := Real.add_one_le_exp (U - Real.log (Z / m))
  have h2 : Real.exp (U - Real.log (Z / m)) = m * Real.exp U / Z := by
    rw [Real.exp_sub, Real.exp_log (div_pos hZ hm)]; field_simp
  rw [h2, Real.log_div hZ.ne' hm.ne'] at h1
  rw [le_div_iff₀ hZ] at h1
  nlinarith

/-- Gibbs variational inequality: `∫ Z U ≤ Ent(Z)` whenever `∫ e^U ≤ 1`. -/
lemma gibbs {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (Z U : α → ℝ) (hZ : ∀ t, 0 < Z t) (hZi : Integrable Z ν)
    (hZl : Integrable (fun t => Z t * Real.log (Z t)) ν)
    (hZU : Integrable (fun t => Z t * U t) ν) (hU : Integrable (fun t => Real.exp (U t)) ν)
    (hU1 : ∫ t, Real.exp (U t) ∂ν ≤ 1) :
    ∫ t, Z t * U t ∂ν ≤ ∫ t, Z t * Real.log (Z t) ∂ν - (∫ t, Z t ∂ν) * Real.log (∫ t, Z t ∂ν) := by
  set m := ∫ t, Z t ∂ν with hm_def
  have hm : 0 < m := by
    rw [hm_def, integral_pos_iff_support_of_nonneg (fun t => (hZ t).le) hZi]
    have : Function.support Z = Set.univ := by
      ext t; simp [(hZ t).ne']
    rw [this]; simp
  have hpt : ∀ t, Z t * U t ≤ Z t * Real.log (Z t) - Z t * Real.log m - Z t
      + m * Real.exp (U t) := fun t => young_scaled (hZ t) hm
  have hint : Integrable (fun t => Z t * Real.log (Z t) - Z t * Real.log m - Z t
      + m * Real.exp (U t)) ν :=
    ((hZl.sub (hZi.mul_const _)).sub hZi).add (hU.const_mul m)
  have h := integral_mono hZU hint hpt
  have hA : Integrable (fun t => Z t * Real.log (Z t) - Z t * Real.log m) ν :=
    hZl.sub (hZi.mul_const _)
  have e1 : ∫ t, (Z t * Real.log (Z t) - Z t * Real.log m - Z t + m * Real.exp (U t)) ∂ν
      = (∫ t, Z t * Real.log (Z t) ∂ν) - m * Real.log m - m + m * ∫ t, Real.exp (U t) ∂ν := by
    rw [integral_add (f := fun t => Z t * Real.log (Z t) - Z t * Real.log m - Z t)
      (g := fun t => m * Real.exp (U t)) (hA.sub hZi) (hU.const_mul m),
      integral_sub (f := fun t => Z t * Real.log (Z t) - Z t * Real.log m) hA hZi,
      integral_sub hZl (hZi.mul_const _), integral_const_mul, integral_mul_const]
  rw [e1] at h
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]

/-- Resampling one coordinate preserves the product measure. -/
lemma mp_update (i : ι) :
    MeasurePreserving (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  refine ⟨measurable_update', ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi (Function.update s i Set.univ) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · have := h j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · have := h1 j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : (fun j => μ j (Function.update s i Set.univ j))
      = Function.update (fun j => μ j (s j)) i 1 := by
    ext1 j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [this, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    ← Finset.mul_prod_erase Finset.univ (fun j => μ j (s j)) (Finset.mem_univ i), mul_comm,
    Finset.sdiff_singleton_eq_erase]

lemma integral_update (i : ι) {F : (ι → Ω) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    ∫ x, F x ∂(Measure.pi μ) = ∫ x, ∫ t, F (Function.update x i t) ∂(μ i) ∂(Measure.pi μ) := by
  have hmp := mp_update μ i
  have hcomp : Integrable (fun p : (ι → Ω) × Ω => F (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) :=
    (hmp.integrable_comp hF.aestronglyMeasurable).2 hF
  rw [← integral_prod _ hcomp]
  conv_lhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)]

lemma integrable_comp_update (i : ι) {F : (ι → Ω) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    Integrable (fun p : (ι → Ω) × Ω => F (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) :=
  ((mp_update μ i).integrable_comp hF.aestronglyMeasurable).2 hF

lemma ae_section_integrable (i : ι) {F : (ι → Ω) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    ∀ᵐ x ∂(Measure.pi μ), Integrable (fun t => F (Function.update x i t)) (μ i) :=
  (integrable_comp_update μ i hF).prod_right_ae

lemma integrable_section_integral (i : ι) {F : (ι → Ω) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    Integrable (fun x => ∫ t, F (Function.update x i t) ∂(μ i)) (Measure.pi μ) :=
  (integrable_comp_update μ i hF).integral_prod_left

lemma ae_ae_update (i : ι) {P : (ι → Ω) → Prop} (hP : ∀ᵐ x ∂(Measure.pi μ), P x) :
    ∀ᵐ x ∂(Measure.pi μ), ∀ᵐ t ∂(μ i), P (Function.update x i t) := by
  have := (mp_update μ i).quasiMeasurePreserving.ae hP
  exact Measure.ae_ae_of_ae_prod this


variable {μ}

/-- A function independent of the coordinates in `S` is fixed by `lmarginal S`. -/
lemma lmarginal_of_indep (S : Finset ι) (F : (ι → Ω) → ℝ≥0∞)
    (hF : ∀ x y, (∀ j ∉ S, x j = y j) → F x = F y) :
    lmarginal μ S F = F := by
  ext x
  simp only [lmarginal]
  have : ∀ y, F (Function.updateFinset x S y) = F x :=
    fun y => hF _ _ (fun j hj => by simp [Function.updateFinset_def, hj])
  simp_rw [this]; simp

lemma lintegral_lmarginal (S : Finset ι) {F : (ι → Ω) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, lmarginal μ S F x ∂(Measure.pi μ) = ∫⁻ x, F x ∂(Measure.pi μ) :=
  lintegral_eq_of_lmarginal_eq S (hF.lmarginal μ) hF
    (lmarginal_of_indep S _ (fun _ _ h => lmarginal_congr μ F h))

lemma lintegral_mul_indep (S : Finset ι) {F W : (ι → Ω) → ℝ≥0∞} (hF : Measurable F)
    (hW : Measurable W) (hWi : ∀ x y, (∀ j ∉ S, x j = y j) → W x = W y) :
    ∫⁻ x, F x * W x ∂(Measure.pi μ) = ∫⁻ x, lmarginal μ S F x * W x ∂(Measure.pi μ) := by
  have h1 : lmarginal μ S (fun x => F x * W x) = fun x => lmarginal μ S F x * W x := by
    ext x; simp only [lmarginal]
    have : ∀ y, W (Function.updateFinset x S y) = W x :=
      fun y => hWi _ _ (fun j hj => by simp [Function.updateFinset_def, hj])
    simp_rw [this]
    exact lintegral_mul_const (f := fun y => F (Function.updateFinset x S y)) _
      (hF.comp measurable_updateFinset)
  have := lintegral_lmarginal (μ := μ) S (F := fun x => F x * W x) (hF.mul hW)
  rw [h1] at this
  exact this.symm

/-- The partial integral `E_S Z`, integrating out the coordinates in `S`. -/
noncomputable def margE (μ : ι → Measure Ω) (S : Finset ι) (Z : (ι → Ω) → ℝ) (x : ι → Ω) : ℝ :=
  (lmarginal μ S (fun y => ENNReal.ofReal (Z y)) x).toReal

section Z
variable {Z : (ι → Ω) → ℝ} (hZm : Measurable Z) (hZ : ∀ x, 0 < Z x)
  (hZi : Integrable Z (Measure.pi μ))

include hZm in
lemma measurable_ofReal_Z : Measurable (fun y => ENNReal.ofReal (Z y)) :=
  ENNReal.measurable_ofReal.comp hZm

include hZm in
lemma margA_measurable (S : Finset ι) :
    Measurable (lmarginal μ S (fun y => ENNReal.ofReal (Z y))) :=
  (measurable_ofReal_Z hZm).lmarginal μ

include hZm in
lemma margE_measurable (S : Finset ι) : Measurable (margE μ S Z) :=
  (margA_measurable hZm S).ennreal_toReal

include hZm hZ in
lemma margA_pos (S : Finset ι) (x : ι → Ω) :
    0 < lmarginal μ S (fun y => ENNReal.ofReal (Z y)) x := by
  simp only [lmarginal]
  rw [lintegral_pos_iff_support (f := fun y => ENNReal.ofReal (Z (Function.updateFinset x S y)))
    ((measurable_ofReal_Z hZm).comp measurable_updateFinset)]
  have : Function.support (fun y : (∀ i : S, Ω) => ENNReal.ofReal (Z (Function.updateFinset x S y)))
      = Set.univ := by
    ext y; simp [hZ]
  rw [this]; simp

include hZm hZi in
lemma lintegral_margA (S : Finset ι) :
    ∫⁻ x, lmarginal μ S (fun y => ENNReal.ofReal (Z y)) x ∂(Measure.pi μ) ≠ ∞ := by
  rw [lintegral_lmarginal S (measurable_ofReal_Z hZm)]
  exact hZi.lintegral_lt_top.ne

include hZm hZi in
lemma ae_margA_lt_top (S : Finset ι) :
    ∀ᵐ x ∂(Measure.pi μ), lmarginal μ S (fun y => ENNReal.ofReal (Z y)) x < ∞ :=
  ae_lt_top (margA_measurable hZm S) (lintegral_margA hZm hZi S)

lemma margE_nonneg (S : Finset ι) (x : ι → Ω) : 0 ≤ margE μ S Z x := ENNReal.toReal_nonneg

include hZm hZ hZi in
lemma ae_margE_pos (S : Finset ι) : ∀ᵐ x ∂(Measure.pi μ), 0 < margE μ S Z x := by
  filter_upwards [ae_margA_lt_top hZm hZi S] with x hx
  exact ENNReal.toReal_pos (margA_pos hZm hZ S x).ne' hx.ne

include hZ in
lemma margE_empty : margE μ ∅ Z = Z := by
  ext x; simp [margE, ENNReal.toReal_ofReal (hZ x).le]

include hZ hZi in
lemma margE_univ (x : ι → Ω) : margE μ Finset.univ Z x = ∫ y, Z y ∂(Measure.pi μ) := by
  simp only [margE, lmarginal_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hZi (Filter.Eventually.of_forall fun y => (hZ y).le),
    ENNReal.toReal_ofReal (integral_nonneg fun y => (hZ y).le)]

lemma margE_congr (S : Finset ι) {x y : ι → Ω} (h : ∀ j ∉ S, x j = y j) :
    margE μ S Z x = margE μ S Z y := by
  simp only [margE]; rw [lmarginal_congr μ _ h]

lemma margE_update_of_mem (S : Finset ι) {i : ι} (hi : i ∈ S) (x : ι → Ω) (t : Ω) :
    margE μ S Z (Function.update x i t) = margE μ S Z x := by
  simp only [margE]; rw [lmarginal_update_of_mem μ hi]

include hZm hZi in
lemma integrable_margE (S : Finset ι) : Integrable (margE μ S Z) (Measure.pi μ) :=
  integrable_toReal_of_lintegral_ne_top (margA_measurable hZm S).aemeasurable
    (lintegral_margA hZm hZi S)


lemma mul_negLog_le {b : ℝ} (hb : 0 ≤ b) : b * max (-Real.log b) 0 ≤ 1 := by
  rcases hb.lt_or_eq with hb | hb
  · rcases le_total 1 b with h1 | h1
    · have : max (-Real.log b) 0 = 0 := by
        rw [max_eq_right]; linarith [Real.log_nonneg h1]
      rw [this]; norm_num
    · have hl := Real.one_sub_inv_le_log_of_pos hb
      have : max (-Real.log b) 0 = -Real.log b := by
        rw [max_eq_left]; linarith [Real.log_nonpos hb.le h1]
      rw [this]
      have : b * (1 - b⁻¹) = b - 1 := by field_simp
      nlinarith
  · subst hb; simp

lemma neg_one_le_mul_log {m : ℝ} (hm : 0 ≤ m) : -1 ≤ m * Real.log m := by
  rcases hm.lt_or_eq with hm | hm
  · have hl := Real.one_sub_inv_le_log_of_pos hm
    have : m * (1 - m⁻¹) = m - 1 := by field_simp
    nlinarith
  · subst hm; simp

include hZm hZ hZi in
lemma integrable_Z_mul_negLog (S : Finset ι) :
    Integrable (fun x => Z x * max (-Real.log (margE μ S Z x)) 0) (Measure.pi μ) := by
  have hmeas : Measurable (fun x => Z x * max (-Real.log (margE μ S Z x)) 0) :=
    hZm.mul (((Real.measurable_log.comp (margE_measurable hZm S)).neg).max measurable_const)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
    mul_nonneg (hZ x).le (le_max_right _ _))]
  have hW : Measurable (fun x => ENNReal.ofReal (max (-Real.log (margE μ S Z x)) 0)) :=
    ENNReal.measurable_ofReal.comp
      (((Real.measurable_log.comp (margE_measurable hZm S)).neg).max measurable_const)
  have e1 : (fun x => ENNReal.ofReal (Z x * max (-Real.log (margE μ S Z x)) 0))
      = fun x => ENNReal.ofReal (Z x) * ENNReal.ofReal (max (-Real.log (margE μ S Z x)) 0) := by
    ext x; rw [ENNReal.ofReal_mul (hZ x).le]
  rw [e1, lintegral_mul_indep S (measurable_ofReal_Z hZm) hW
    (fun x y h => by simp only [margE_congr S h])]
  calc ∫⁻ x, lmarginal μ S (fun y => ENNReal.ofReal (Z y)) x
          * ENNReal.ofReal (max (-Real.log (margE μ S Z x)) 0) ∂(Measure.pi μ)
        ≤ ∫⁻ _x, 1 ∂(Measure.pi μ) := by
          refine lintegral_mono fun x => ?_
          simp only [margE]
          set A := lmarginal μ S (fun y => ENNReal.ofReal (Z y)) x
          rcases eq_or_ne A ∞ with hA | hA
          · rw [hA]; simp
          · rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
            exact ENNReal.ofReal_le_one.2 (mul_negLog_le ENNReal.toReal_nonneg)
    _ < ∞ := by simp

include hZm hZ hZi in
lemma integrable_Z_mul_log_margE (hZl : Integrable (fun x => Z x * Real.log (Z x)) (Measure.pi μ))
    (S : Finset ι) :
    Integrable (fun x => Z x * Real.log (margE μ S Z x)) (Measure.pi μ) := by
  refine Integrable.mono' (((hZl.abs.add hZi).add (integrable_margE hZm hZi S)).add
    (integrable_Z_mul_negLog hZm hZ hZi S))
    (hZm.mul (Real.measurable_log.comp (margE_measurable hZm S))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hZx := hZ x
  have hb := margE_nonneg (μ := μ) S (Z := Z) x
  set b := margE μ S Z x
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have hn : 0 ≤ max (-Real.log b) 0 := le_max_right _ _
  have hn2 : -Real.log b ≤ max (-Real.log b) 0 := le_max_left _ _
  rcases hb.lt_or_eq with hb | hb
  · have hy := young_scaled (U := Real.log b) hZx one_pos
    rw [Real.log_one, Real.exp_log hb] at hy
    have hlow : -(Z x * max (-Real.log b) 0) ≤ Z x * Real.log b := by nlinarith
    have := abs_nonneg (Z x * Real.log (Z x))
    have := le_abs_self (Z x * Real.log (Z x))
    have := mul_nonneg hZx.le hn
    rw [abs_le]; constructor <;> nlinarith
  · rw [← hb, Real.log_zero, mul_zero, abs_zero]
    have := abs_nonneg (Z x * Real.log (Z x))
    have := mul_nonneg hZx.le hn
    linarith

/-- The `i`-th one-coordinate entropy of `Z` at `x`. -/
noncomputable def entI (μ : ι → Measure Ω) (i : ι) (Z : (ι → Ω) → ℝ) (x : ι → Ω) : ℝ :=
  ∫ t, Z (Function.update x i t) * Real.log (Z (Function.update x i t)) ∂(μ i)
    - (∫ t, Z (Function.update x i t) ∂(μ i)) * Real.log (∫ t, Z (Function.update x i t) ∂(μ i))

lemma stronglyMeasurable_section_integral (i : ι) {G : (ι → Ω) → ℝ} (hG : Measurable G) :
    StronglyMeasurable (fun x => ∫ t, G (Function.update x i t) ∂(μ i)) :=
  StronglyMeasurable.integral_prod_right' (f := fun p : (ι → Ω) × Ω => G (Function.update p.1 i p.2))
    (hG.comp measurable_update').stronglyMeasurable

include hZm hZ hZi in
lemma step_bound (hZl : Integrable (fun x => Z x * Real.log (Z x)) (Measure.pi μ))
    (S : Finset ι) (i : ι) (hi : i ∉ S) :
    ∫ x, Z x * (Real.log (margE μ S Z x) - Real.log (margE μ (insert i S) Z x)) ∂(Measure.pi μ)
      ≤ ∫ x, entI μ i Z x ∂(Measure.pi μ) := by
  set U := fun x => Real.log (margE μ S Z x) - Real.log (margE μ (insert i S) Z x) with hU_def
  have hZU : Integrable (fun x => Z x * U x) (Measure.pi μ) := by
    have := (integrable_Z_mul_log_margE hZm hZ hZi hZl S).sub
      (integrable_Z_mul_log_margE hZm hZ hZi hZl (insert i S))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hU_def, Pi.sub_apply]; ring
  have hUm : Measurable U :=
    (Real.measurable_log.comp (margE_measurable hZm S)).sub
      (Real.measurable_log.comp (margE_measurable hZm (insert i S)))
  rw [integral_update μ i hZU]
  have hinner := integrable_section_integral μ i hZU
  -- the pointwise Gibbs bound
  have key : ∀ x, Integrable (fun t => Z (Function.update x i t)) (μ i) →
      Integrable (fun t => Z (Function.update x i t) * Real.log (Z (Function.update x i t))) (μ i) →
      Integrable (fun t => Z (Function.update x i t) * U (Function.update x i t)) (μ i) →
      lmarginal μ (insert i S) (fun y => ENNReal.ofReal (Z y)) x < ∞ →
      ∫ t, Z (Function.update x i t) * U (Function.update x i t) ∂(μ i) ≤ entI μ i Z x := by
    intro x h1 h2 h3 h4
    set c := margE μ (insert i S) Z x with hc_def
    have hc : 0 < c := ENNReal.toReal_pos (margA_pos hZm hZ _ x).ne' h4.ne
    have hcu : ∀ t, margE μ (insert i S) Z (Function.update x i t) = c := fun t =>
      margE_update_of_mem (insert i S) (Finset.mem_insert_self i S) x t
    have hins := lmarginal_insert (μ := μ) _ (measurable_ofReal_Z hZm) hi x
    have hmeasA : Measurable (fun t => lmarginal μ S (fun y => ENNReal.ofReal (Z y))
        (Function.update x i t)) := (margA_measurable hZm S).comp (measurable_update x)
    have hfin : ∫⁻ t, lmarginal μ S (fun y => ENNReal.ofReal (Z y)) (Function.update x i t)
        ∂(μ i) ≠ ∞ := by rw [← hins]; exact h4.ne
    have hae := ae_lt_top hmeasA hfin
    have hexp : (fun t => Real.exp (U (Function.update x i t)))
        =ᵐ[μ i] fun t => margE μ S Z (Function.update x i t) / c := by
      filter_upwards [hae] with t ht
      have hpos : 0 < margE μ S Z (Function.update x i t) :=
        ENNReal.toReal_pos (margA_pos hZm hZ _ _).ne' ht.ne
      simp only [hU_def, hcu, Real.exp_sub, Real.exp_log hpos, Real.exp_log hc]
    have hintE : Integrable (fun t => margE μ S Z (Function.update x i t)) (μ i) :=
      integrable_toReal_of_lintegral_ne_top hmeasA.aemeasurable hfin
    have hint1 : ∫ t, margE μ S Z (Function.update x i t) ∂(μ i) = c := by
      simp only [margE]
      rw [integral_toReal hmeasA.aemeasurable hae, ← hins]
      rfl
    refine gibbs (μ i) (fun t => Z (Function.update x i t)) (fun t => U (Function.update x i t))
      (fun t => hZ _) h1 h2 h3 ((hintE.div_const c).congr hexp.symm) ?_
    rw [integral_congr_ae hexp, integral_div, hint1, div_self hc.ne']
  have hae1 := ae_section_integrable μ i hZi
  have hae2 := ae_section_integrable μ i hZl
  have hae3 := ae_section_integrable μ i hZU
  have hae4 := ae_margA_lt_top hZm hZi (insert i S)
  have hbound : ∀ᵐ x ∂(Measure.pi μ),
      ∫ t, Z (Function.update x i t) * U (Function.update x i t) ∂(μ i) ≤ entI μ i Z x := by
    filter_upwards [hae1, hae2, hae3, hae4] with x h1 h2 h3 h4 using key x h1 h2 h3 h4
  -- integrability of the one-coordinate entropy
  have hmeasEnt : Measurable (entI μ i Z) := by
    have m1 := (stronglyMeasurable_section_integral (μ := μ) i
      (hZm.mul (Real.measurable_log.comp hZm))).measurable
    have m2 := (stronglyMeasurable_section_integral (μ := μ) i hZm).measurable
    exact m1.sub (m2.mul (Real.measurable_log.comp m2))
  have hup := integrable_section_integral μ i hZl
  have hEnt : Integrable (entI μ i Z) (Measure.pi μ) := by
    refine Integrable.mono' ((hinner.abs.add hup.abs).add (integrable_const 1))
      hmeasEnt.aestronglyMeasurable ?_
    filter_upwards [hbound] with x hx
    have hm0 : 0 ≤ ∫ t, Z (Function.update x i t) ∂(μ i) :=
      integral_nonneg fun t => (hZ _).le
    have hml := neg_one_le_mul_log hm0
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have hEdef : entI μ i Z x = (∫ t, Z (Function.update x i t) *
        Real.log (Z (Function.update x i t)) ∂(μ i))
        - (∫ t, Z (Function.update x i t) ∂(μ i))
          * Real.log (∫ t, Z (Function.update x i t) ∂(μ i)) := rfl
    rw [abs_le]
    constructor
    · have := neg_abs_le (∫ t, Z (Function.update x i t) * U (Function.update x i t) ∂(μ i))
      have := abs_nonneg (∫ t, Z (Function.update x i t) *
        Real.log (Z (Function.update x i t)) ∂(μ i))
      linarith
    · have := le_abs_self (∫ t, Z (Function.update x i t) *
        Real.log (Z (Function.update x i t)) ∂(μ i))
      have := abs_nonneg (∫ t, Z (Function.update x i t) * U (Function.update x i t) ∂(μ i))
      rw [hEdef]; linarith
  exact integral_mono_ae hinner hEnt hbound


include hZm hZ hZi in
lemma telescope (hZl : Integrable (fun x => Z x * Real.log (Z x)) (Measure.pi μ))
    (S : Finset ι) :
    ∫ x, Z x * Real.log (Z x) ∂(Measure.pi μ) - ∫ x, Z x * Real.log (margE μ S Z x) ∂(Measure.pi μ)
      ≤ ∑ i ∈ S, ∫ x, entI μ i Z x ∂(Measure.pi μ) := by
  induction S using Finset.induction_on with
  | empty => simp [margE_empty hZ]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    have hstep := step_bound hZm hZ hZi hZl S i hi
    have e : ∫ x, Z x * (Real.log (margE μ S Z x) - Real.log (margE μ (insert i S) Z x))
        ∂(Measure.pi μ) = ∫ x, Z x * Real.log (margE μ S Z x) ∂(Measure.pi μ)
          - ∫ x, Z x * Real.log (margE μ (insert i S) Z x) ∂(Measure.pi μ) := by
      rw [← integral_sub (integrable_Z_mul_log_margE hZm hZ hZi hZl S)
        (integrable_Z_mul_log_margE hZm hZ hZi hZl (insert i S))]
      congr 1; ext x; ring
    rw [e] at hstep
    linarith

end Z

end GaussianMatrix.EntTensor

open GaussianMatrix

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (h : (ι → Ω) → ℝ) (hmeas : Measurable h) (hpos : ∀ x, 0 < h x)
    (hint : Integrable h (Measure.pi μ))
    (hlog : Integrable (fun x => h x * Real.log (h x)) (Measure.pi μ)) :
    ∫ x, h x * Real.log (h x) ∂(Measure.pi μ)
      - (∫ x, h x ∂(Measure.pi μ)) * Real.log (∫ x, h x ∂(Measure.pi μ))
      ≤ ∑ i, ∫ x, (∫ t, h (Function.update x i t) * Real.log (h (Function.update x i t)) ∂(μ i)
          - (∫ t, h (Function.update x i t) ∂(μ i))
            * Real.log (∫ t, h (Function.update x i t) ∂(μ i))) ∂(Measure.pi μ) := by
  have ht := GaussianMatrix.EntTensor.telescope hmeas hpos hint hlog Finset.univ
  simp only [GaussianMatrix.EntTensor.margE_univ hpos hint, integral_mul_const] at ht
  exact ht
