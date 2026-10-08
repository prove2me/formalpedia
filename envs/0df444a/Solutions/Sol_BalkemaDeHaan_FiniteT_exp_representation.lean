-- Prove2me | solution 1 for BalkemaDeHaan.FiniteT.exp_representation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:02:28.846261+00:00
-- url     : https://prove2.me/submissions/8d1ce41c-c523-4209-b38f-26affee905bb

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory


namespace BalkemaDeHaan.FiniteT

lemma real_Ioi_d3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (μ (Set.Ioi t)).toReal = 1 - cdf μ t := by
  have h1 : μ (Set.Ioi t) = 1 - ENNReal.ofReal (cdf μ t) := by
    rw [ofReal_cdf, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
  rw [h1, ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.mpr (cdf_le_one μ t)) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofReal (cdf_nonneg μ t)]

lemma real_Ioc_d3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ) (hab : a ≤ b) :
    (μ (Set.Ioc a b)).toReal = cdf μ b - cdf μ a := by
  have := StieltjesFunction.measure_Ioc (cdf μ) a b
  rw [measure_cdf] at this
  rw [this, ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_cdf μ hab))]

/-- The survival function is positive on `[t₀, ∞)`. -/
lemma surv_pos_d3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f') (t : ℝ) (ht : t₀ ≤ t) : 0 < 1 - cdf μ t := by
  rcases (sub_nonneg.mpr (cdf_le_one μ t)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hconst : ∀ u, t ≤ u → cdf μ u = 1 := fun u hu =>
      le_antisymm (cdf_le_one μ u) (by have := monotone_cdf μ hu; linarith)
    have h1 := hdens (t + 1) (by linarith)
    have hd' : HasDerivAt (cdf μ) (f (t + 1)) (t + 1) :=
      h1.1.hasDerivAt (Ici_mem_nhds (by linarith))
    have hd2 : HasDerivAt (cdf μ) 0 (t + 1) := by
      have hev : cdf μ =ᶠ[nhds (t + 1)] (fun _ => (1 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds (show t < t + 1 by linarith)] with u hu
        exact hconst u (le_of_lt hu)
      exact (hasDerivAt_const (t + 1) (1 : ℝ)).congr_of_eventuallyEq hev
    have := hd'.unique hd2
    linarith [h1.2.1]

lemma normA_pos_d3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f') (t : ℝ) (ht : t₀ ≤ t) : 0 < normA μ f t :=
  div_pos (surv_pos_d3 μ t₀ f f' hdens t ht) (hdens t ht).2.1

lemma cdf_continuousOn_d3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f') : ContinuousOn (cdf μ) (Set.Ici t₀) :=
  fun t ht => (hdens t ht).1.continuousWithinAt

lemma normA_continuousOn_d3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f') : ContinuousOn (normA μ f) (Set.Ici t₀) := by
  have h1 : ContinuousOn (fun t => 1 - cdf μ t) (Set.Ici t₀) :=
    continuousOn_const.sub (cdf_continuousOn_d3 μ t₀ f f' hdens)
  have h2 : ContinuousOn f (Set.Ici t₀) := fun t ht => (hdens t ht).2.2.continuousWithinAt
  exact h1.div h2 (fun t ht => (hdens t ht).2.1.ne')

theorem exp_representation_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f') :
    ∀ t ≥ t₀, ∀ x : ℝ, 0 ≤ x →
      1 - BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t)
          = (1 - cdf μ (t + x * normA μ f t)) / (1 - cdf μ t) ∧
        (1 - cdf μ (t + x * normA μ f t)) / (1 - cdf μ t)
          = Real.exp (-∫ s in (0 : ℝ)..x, normA μ f t / normA μ f (t + s * normA μ f t)) := by
  intro t ht x hx
  have hFt := surv_pos_d3 μ t₀ f f' hdens t ht
  have hat := normA_pos_d3 μ t₀ f f' hdens t ht
  have hpt : ∀ s, 0 ≤ s → t₀ ≤ t + s * normA μ f t := fun s hs => by nlinarith
  have hmaps : Set.MapsTo (fun s => t + s * normA μ f t) (Set.Icc 0 x) (Set.Ici t₀) :=
    fun s hs => hpt s hs.1
  have hlin : ContinuousOn (fun s : ℝ => t + s * normA μ f t) (Set.Icc 0 x) :=
    continuousOn_const.add (continuousOn_id.mul continuousOn_const)
  constructor
  · have htb : t ≤ t + x * normA μ f t := by nlinarith
    rw [BalkemaDeHaan.ParetoBounds.residualLife, real_Ioi_d3, real_Ioc_d3 μ _ _ htb]
    field_simp
    ring
  · have key : ∫ s in (0 : ℝ)..x, normA μ f t / normA μ f (t + s * normA μ f t)
        = -Real.log (1 - cdf μ (t + x * normA μ f t))
          - (-Real.log (1 - cdf μ (t + 0 * normA μ f t))) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
      · have hc : ContinuousOn (fun s => 1 - cdf μ (t + s * normA μ f t)) (Set.Icc 0 x) :=
          continuousOn_const.sub ((cdf_continuousOn_d3 μ t₀ f f' hdens).comp hlin hmaps)
        exact (hc.log (fun s hs => (surv_pos_d3 μ t₀ f f' hdens _ (hpt s hs.1)).ne')).neg
      · intro s hs
        have hu : t₀ < t + s * normA μ f t := by nlinarith [hs.1]
        have hF : HasDerivAt (cdf μ) (f (t + s * normA μ f t)) (t + s * normA μ f t) :=
          (hdens _ hu.le).1.hasDerivAt (Ici_mem_nhds hu)
        have hcomp : HasDerivAt (fun s => cdf μ (t + s * normA μ f t))
            (f (t + s * normA μ f t) * normA μ f t) s := by
          have hl : HasDerivAt (fun s : ℝ => t + s * normA μ f t) (normA μ f t) s := by
            simpa using ((hasDerivAt_id s).mul_const (normA μ f t)).const_add t
          exact hF.comp s hl
        have hpos : 0 < 1 - cdf μ (t + s * normA μ f t) := surv_pos_d3 μ t₀ f f' hdens _ hu.le
        have hlog : HasDerivAt (fun s => Real.log (1 - cdf μ (t + s * normA μ f t)))
            ((0 - f (t + s * normA μ f t) * normA μ f t) / (1 - cdf μ (t + s * normA μ f t))) s :=
          ((hasDerivAt_const s (1 : ℝ)).sub hcomp).log hpos.ne'
        have hfpos := (hdens _ hu.le).2.1
        refine hlog.neg.congr_deriv ?_
        show _ = normA μ f t / ((1 - cdf μ (t + s * normA μ f t)) / f (t + s * normA μ f t))
        field_simp
        ring
      · apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hx]
        have hc : ContinuousOn (fun s => normA μ f (t + s * normA μ f t)) (Set.Icc 0 x) :=
          (normA_continuousOn_d3 μ t₀ f f' hdens).comp hlin hmaps
        exact continuousOn_const.div hc
          (fun s hs => (normA_pos_d3 μ t₀ f f' hdens _ (hpt s hs.1)).ne')
    rw [key]
    simp only [zero_mul, add_zero]
    have hFb := surv_pos_d3 μ t₀ f f' hdens _ (hpt x hx)
    rw [show -(-Real.log (1 - cdf μ (t + x * normA μ f t)) - -Real.log (1 - cdf μ t))
        = Real.log (1 - cdf μ (t + x * normA μ f t)) - Real.log (1 - cdf μ t) by ring,
      Real.exp_sub, Real.exp_log hFb, Real.exp_log hFt]

theorem bounds_13_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' a' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f')
    (ha' : ∀ t ≥ t₀, HasDerivWithinAt (normA μ f) (a' t) (Set.Ici t₀) t)
    (c₁ c₂ : ℝ) (hc : ∀ t ≥ t₀, c₁ ≤ a' t ∧ a' t ≤ c₂) :
    ∀ t ≥ t₀, ∀ x : ℝ, 0 ≤ x →
      (c₁ * x * normA μ f t ≤ normA μ f (t + x * normA μ f t) - normA μ f t ∧
        normA μ f (t + x * normA μ f t) - normA μ f t ≤ c₂ * x * normA μ f t) ∧
      (1 + c₁ * x ≤ normA μ f (t + x * normA μ f t) / normA μ f t ∧
        normA μ f (t + x * normA μ f t) / normA μ f t ≤ 1 + c₂ * x) := by
  intro t ht x hx
  have hat := normA_pos_d3 μ t₀ f f' hdens t ht
  have htb : t ≤ t + x * normA μ f t := by nlinarith
  have hcont : ContinuousOn (normA μ f) (Set.Icc t (t + x * normA μ f t)) :=
    (normA_continuousOn_d3 μ t₀ f f' hdens).mono (fun u hu => le_trans ht hu.1)
  have hderiv : ∀ u ∈ interior (Set.Icc t (t + x * normA μ f t)),
      HasDerivAt (normA μ f) (a' u) u := by
    intro u hu
    rw [interior_Icc] at hu
    exact (ha' u (by linarith [hu.1])).hasDerivAt (Ici_mem_nhds (by linarith [hu.1]))
  have hdiff : DifferentiableOn ℝ (normA μ f) (interior (Set.Icc t (t + x * normA μ f t))) :=
    fun u hu => (hderiv u hu).differentiableAt.differentiableWithinAt
  have hmem1 : t ∈ Set.Icc t (t + x * normA μ f t) := ⟨le_rfl, htb⟩
  have hmem2 : t + x * normA μ f t ∈ Set.Icc t (t + x * normA μ f t) := ⟨htb, le_rfl⟩
  have h1 := (convex_Icc _ _).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun u hu => by
      rw [(hderiv u hu).deriv]
      rw [interior_Icc] at hu
      exact (hc u (by linarith [hu.1])).1) t hmem1 _ hmem2 htb
  have h2 := (convex_Icc _ _).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun u hu => by
      rw [(hderiv u hu).deriv]
      rw [interior_Icc] at hu
      exact (hc u (by linarith [hu.1])).2) t hmem1 _ hmem2 htb
  have e1 : c₁ * (t + x * normA μ f t - t) = c₁ * x * normA μ f t := by ring
  have e2 : c₂ * (t + x * normA μ f t - t) = c₂ * x * normA μ f t := by ring
  rw [e1] at h1
  rw [e2] at h2
  refine ⟨⟨h1, h2⟩, ?_, ?_⟩
  · rw [le_div_iff₀ hat]; linarith
  · rw [div_le_iff₀ hat]; linarith

end BalkemaDeHaan.FiniteT

open BalkemaDeHaan.FiniteT


theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (t₀ : ℝ) (f f' : ℝ → ℝ)
    (hdens : HasPosDiffDensity μ t₀ f f') :
    ∀ t ≥ t₀, ∀ x : ℝ, 0 ≤ x →
      1 - BalkemaDeHaan.ParetoBounds.residualLife μ t (x * normA μ f t)
          = (1 - cdf μ (t + x * normA μ f t)) / (1 - cdf μ t) ∧
        (1 - cdf μ (t + x * normA μ f t)) / (1 - cdf μ t)
          = Real.exp (-∫ s in (0 : ℝ)..x, normA μ f t / normA μ f (t + s * normA μ f t)) := by
  exact exp_representation_core μ t₀ f f' hdens
