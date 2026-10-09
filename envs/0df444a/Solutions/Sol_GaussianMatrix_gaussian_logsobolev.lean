-- Prove2me | solution 1 for GaussianMatrix.gaussian_logsobolev
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:56:01.98923+00:00
-- url     : https://prove2.me/submissions/ee4a31c9-e32f-4685-b601-69570503c0e5

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_gaussian_logsobolev_one_dim
import Theorems.Thm_GaussianMatrix_entropy_tensorization

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix.LSIMulti

lemma mp_update {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  refine ⟨measurable_update', ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have : (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (Function.update s i Set.univ) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [this, Measure.prod_prod, Measure.pi_pi,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul Finset.univ (fun j => μ j (s j)) (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma mul_log_bound (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    |(a + δ) * Real.log (a + δ)| ≤ |a * Real.log a| + a + 2 := by
  set b := a + δ with hb
  have hbpos : 0 < b := by positivity
  -- convexity: a log a ≥ a log b + a - b
  have hconv : a * Real.log b + a - b ≤ a * Real.log a := by
    rcases ha.eq_or_lt with h0 | hpos
    · subst h0; simp; linarith
    · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hpos hbpos)
      rw [Real.log_div hpos.ne' hbpos.ne', inv_div] at h1
      have h2 : a * (1 - b / a) ≤ a * (Real.log a - Real.log b) :=
        mul_le_mul_of_nonneg_left h1 ha
      rw [mul_sub, mul_div_cancel₀ _ hpos.ne'] at h2
      linarith
  rcases le_or_gt 1 b with hb1 | hb1
  · have hlog0 : 0 ≤ Real.log b := Real.log_nonneg hb1
    have hlogb : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hbpos
    rw [abs_of_nonneg (mul_nonneg hbpos.le hlog0)]
    have : b * Real.log b ≤ a * Real.log a + δ * (Real.log b + 1) := by
      have : b * Real.log b = a * Real.log b + δ * Real.log b := by rw [hb]; ring
      linarith
    have h3 : δ * (Real.log b + 1) ≤ Real.log b + 1 := by nlinarith
    have h4 := le_abs_self (a * Real.log a)
    linarith
  · have hlog0 : Real.log b ≤ 0 := Real.log_nonpos hbpos.le hb1.le
    have hl := Real.one_sub_inv_le_log_of_pos hbpos
    have : b * (1 - b⁻¹) ≤ b * Real.log b := mul_le_mul_of_nonneg_left hl hbpos.le
    rw [mul_sub, mul_inv_cancel₀ hbpos.ne', mul_one] at this
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hbpos.le hlog0)]
    have := abs_nonneg (a * Real.log a)
    linarith


section Fubini
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (i : ι)

lemma integrable_comp_update {F : (ι → Ω) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    Integrable (fun p : (ι → Ω) × Ω => F (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) :=
  ((mp_update μ i).integrable_comp hF.aestronglyMeasurable).2 hF

lemma integral_update_eq {F : (ι → Ω) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    ∫ x, ∫ t, F (Function.update x i t) ∂(μ i) ∂(Measure.pi μ) = ∫ x, F x ∂(Measure.pi μ) := by
  have hmp := mp_update μ i
  rw [← integral_prod _ (integrable_comp_update μ i hF)]
  calc ∫ p, F (Function.update p.1 i p.2) ∂((Measure.pi μ).prod (μ i))
      = ∫ x, F x ∂(Measure.map (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2)
          ((Measure.pi μ).prod (μ i))) :=
        (integral_map hmp.measurable.aemeasurable
          (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)).symm
    _ = ∫ x, F x ∂(Measure.pi μ) := by rw [hmp.map_eq]

lemma integrable_section_ae {F : (ι → Ω) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    ∀ᵐ x ∂(Measure.pi μ), Integrable (fun t => F (Function.update x i t)) (μ i) :=
  (integrable_comp_update μ i hF).prod_right_ae

lemma integrable_integral_update {F : (ι → Ω) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    Integrable (fun x => ∫ t, F (Function.update x i t) ∂(μ i)) (Measure.pi μ) :=
  (integrable_comp_update μ i hF).integral_prod_left

end Fubini

/-- One-dimensional step: the `i`-th local entropy of `g ^ 2 + δ` is bounded by the
`i`-th partial energy, whenever the relevant sections are integrable. -/
lemma local_step {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g) (δ : ℝ) (hδ : 0 < δ) (x : ι → ℝ) (i : ι)
    (h1 : Integrable (fun t => g (Function.update x i t) ^ 2) (gaussianReal 0 1))
    (h2 : Integrable (fun t => (g (Function.update x i t) ^ 2 + δ)
      * Real.log (g (Function.update x i t) ^ 2 + δ)) (gaussianReal 0 1))
    (h3 : Integrable (fun t => fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2)
      (gaussianReal 0 1)) :
    ∫ t, (g (Function.update x i t) ^ 2 + δ) * Real.log (g (Function.update x i t) ^ 2 + δ)
        ∂(gaussianReal 0 1)
      - (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
        * Real.log (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2 ∂(gaussianReal 0 1) := by
  set u : ℝ → ℝ := fun t => g (Function.update x i t) with hu_def
  set D : ℝ → ℝ := fun t => fderiv ℝ g (Function.update x i t) (Pi.single i 1) with hD_def
  set φ : ℝ → ℝ := fun t => Real.sqrt (u t ^ 2 + δ) with hφ_def
  have hpos : ∀ t, 0 < u t ^ 2 + δ := fun t => by positivity
  have hu : ∀ t, HasDerivAt u (D t) t := fun t =>
    ((hg.differentiable one_ne_zero) (Function.update x i t)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_update x i t)
  have hφd : ∀ t, HasDerivAt φ ((2 * u t * D t) / (2 * Real.sqrt (u t ^ 2 + δ))) t := by
    intro t
    have h2 : HasDerivAt (fun y => u y ^ 2 + δ) (2 * u t * D t) t := by
      simpa using ((hu t).pow 2).add_const δ
    exact h2.sqrt (hpos t).ne'
  have hsq : ∀ t, φ t ^ 2 = u t ^ 2 + δ := fun t => Real.sq_sqrt (hpos t).le
  have hderiv_sq : ∀ t, deriv φ t ^ 2 ≤ D t ^ 2 := by
    intro t
    rw [(hφd t).deriv, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (hpos t).le]
    rw [div_le_iff₀ (by have := hpos t; positivity)]
    have := sq_nonneg (D t)
    nlinarith [sq_nonneg (u t * D t), mul_nonneg hδ.le this]
  have hφC : ContDiff ℝ 1 φ :=
    (((hg.comp (contDiff_update 1 x i)).pow 2).add contDiff_const).sqrt (fun t => (hpos t).ne')
  have hφ2 : Integrable (fun t => φ t ^ 2) (gaussianReal 0 1) := by
    simp only [hsq]; exact h1.add (integrable_const δ)
  have hφlog : Integrable (fun t => φ t ^ 2 * Real.log (φ t ^ 2)) (gaussianReal 0 1) := by
    simp only [hsq]; exact h2
  have hφd2 : Integrable (fun t => deriv φ t ^ 2) (gaussianReal 0 1) := by
    refine h3.mono' ((hφC.continuous_deriv le_rfl).pow 2).aestronglyMeasurable
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hderiv_sq t
  have key := gaussian_logsobolev_one_dim φ hφC hφ2 hφlog hφd2
  simp only [hsq] at key
  refine key.trans ?_
  gcongr
  intro t
  exact hderiv_sq t


lemma integrable_shift_mul_log {ι : Type*} [Fintype ι] (g : (ι → ℝ) → ℝ)
    (hg : Continuous g)
    (hg2 : Integrable (fun x => g x ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Integrable (fun x => (g x ^ 2 + δ) * Real.log (g x ^ 2 + δ))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine Integrable.mono' ((hglog.abs.add hg2).add (integrable_const (2 : ℝ)))
    ((Real.continuous_mul_log.comp ((hg.pow 2).add continuous_const)).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  exact mul_log_bound (g x ^ 2) δ (sq_nonneg _) hδ hδ1

/-- The regularized inequality: `Ent(g² + δ) ≤ 2 ∫ |∇g|²` for `0 < δ ≤ 1`. -/
lemma ent_delta_le {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdg : Integrable (fun x => ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ x, (g x ^ 2 + δ) * Real.log (g x ^ 2 + δ) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      - (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1) + δ)
        * Real.log (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1) + δ)
      ≤ 2 * ∫ x, ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  set P := Measure.pi fun _ : ι => gaussianReal 0 1 with hP
  have hgc : Continuous g := hg.continuous
  have hmeas : Measurable (fun x => g x ^ 2 + δ) :=
    ((hgc.pow 2).add continuous_const).measurable
  have hpos : ∀ x, 0 < g x ^ 2 + δ := fun x => by positivity
  have hint : Integrable (fun x => g x ^ 2 + δ) P := hg2.add (integrable_const δ)
  have hlogI := integrable_shift_mul_log g hgc hg2 hglog δ hδ hδ1
  have htens := entropy_tensorization (fun _ : ι => gaussianReal 0 1) (fun x => g x ^ 2 + δ)
    hmeas hpos hint hlogI
  have hintc : ∫ x, (g x ^ 2 + δ) ∂P = ∫ x, g x ^ 2 ∂P + δ := by
    rw [integral_add hg2 (integrable_const δ)]
    simp
  rw [← hP, hintc] at htens
  refine htens.trans ?_
  -- partial derivatives
  have hDc : ∀ i, Continuous (fun x => fderiv ℝ g x (Pi.single i 1)) := fun i =>
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDi : ∀ i, Integrable (fun x => fderiv ℝ g x (Pi.single i 1) ^ 2) P := by
    intro i
    refine hdg.mono' ((hDc i).pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun j => fderiv ℝ g x (Pi.single j 1) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hterm : ∀ i, ∫ x, (∫ t, (g (Function.update x i t) ^ 2 + δ)
        * Real.log (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1)
      - (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
        * Real.log (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))) ∂P
      ≤ 2 * ∫ x, fderiv ℝ g x (Pi.single i 1) ^ 2 ∂P := by
    intro i
    have hae : ∀ᵐ x ∂P, (∫ t, (g (Function.update x i t) ^ 2 + δ)
          * Real.log (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1)
        - (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
          * Real.log (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1)))
        ≤ 2 * ∫ t, fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2
          ∂(gaussianReal 0 1) := by
      filter_upwards [integrable_section_ae (fun _ : ι => gaussianReal 0 1) i hg2,
        integrable_section_ae (fun _ : ι => gaussianReal 0 1) i hlogI,
        integrable_section_ae (fun _ : ι => gaussianReal 0 1) i (hDi i)] with x h1 h2 h3
      exact local_step g hg δ hδ x i h1 h2 h3
    have hR : Integrable (fun x => 2 * ∫ t, fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2
        ∂(gaussianReal 0 1)) P :=
      (integrable_integral_update (fun _ : ι => gaussianReal 0 1) i (hDi i)).const_mul 2
    calc _ ≤ ∫ x, 2 * ∫ t, fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2
          ∂(gaussianReal 0 1) ∂P := by
          by_cases hE : Integrable (fun x => ∫ t, (g (Function.update x i t) ^ 2 + δ)
              * Real.log (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1)
            - (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
              * Real.log (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))) P
          · exact integral_mono_ae hE hR hae
          · rw [integral_undef hE]
            exact integral_nonneg fun x =>
              mul_nonneg zero_le_two (integral_nonneg fun t => sq_nonneg _)
      _ = 2 * ∫ x, fderiv ℝ g x (Pi.single i 1) ^ 2 ∂P := by
          rw [integral_const_mul,
            integral_update_eq (fun _ : ι => gaussianReal 0 1) i (hDi i)]
  refine (Finset.sum_le_sum fun i _ => hterm i).trans_eq ?_
  rw [← Finset.mul_sum, integral_finsetSum _ fun i _ => hDi i]

end GaussianMatrix.LSIMulti

open GaussianMatrix

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdg : Integrable (fun x => ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      - (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
        * Real.log (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
      ≤ 2 * ∫ x, ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  set P := Measure.pi fun _ : ι => gaussianReal 0 1 with hP
  set c := ∫ x, g x ^ 2 ∂P with hc
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδ_def
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδle : ∀ n, δ n ≤ 1 := fun n => by
    simp only [hδ_def]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hδlim : Filter.Tendsto δ Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hgc : Continuous g := hg.continuous
  -- first term: dominated convergence
  have hT1 : Filter.Tendsto (fun n => ∫ x, (g x ^ 2 + δ n) * Real.log (g x ^ 2 + δ n) ∂P)
      Filter.atTop (nhds (∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |g x ^ 2 * Real.log (g x ^ 2)| + g x ^ 2 + 2)
      (fun n => (Real.continuous_mul_log.comp
        ((hgc.pow 2).add continuous_const)).aestronglyMeasurable)
      ((hglog.abs.add hg2).add (integrable_const (2 : ℝ)))
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs]
      exact LSIMulti.mul_log_bound (g x ^ 2) (δ n) (sq_nonneg _) (hδpos n) (hδle n)
    · have h1 : Filter.Tendsto (fun n => g x ^ 2 + δ n) Filter.atTop (nhds (g x ^ 2)) := by
        simpa using (tendsto_const_nhds (x := g x ^ 2)).add hδlim
      exact (Real.continuous_mul_log.tendsto (g x ^ 2)).comp h1
  have hT2 : Filter.Tendsto (fun n => (c + δ n) * Real.log (c + δ n))
      Filter.atTop (nhds (c * Real.log c)) := by
    have h1 : Filter.Tendsto (fun n => c + δ n) Filter.atTop (nhds c) := by
      simpa using (tendsto_const_nhds (x := c)).add hδlim
    exact (Real.continuous_mul_log.tendsto c).comp h1
  exact le_of_tendsto' (hT1.sub hT2) fun n =>
    LSIMulti.ent_delta_le g hg hg2 hglog hdg (δ n) (hδpos n) (hδle n)
