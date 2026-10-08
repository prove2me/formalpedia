-- Prove2me | solution 1 for BalkemaDeHaan.ParetoBounds.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:31:14.075792+00:00
-- url     : https://prove2.me/submissions/2b1e3717-6493-46c7-8e4b-f29175088bdf

import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_ResidualLife
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw

open MeasureTheory ProbabilityTheory


namespace BalkemaDeHaan.ParetoBounds

/-- Basic consequences of the hazard bounds. -/
lemma hazard_basic6 (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂)
    (u : ℝ) (hu : t₀ ≤ u) :
    0 < 1 - cdf μ u ∧ 0 < u := by
  obtain ⟨_, hf⟩ := hdens u hu
  obtain ⟨h1, h2⟩ := hbounds u hu
  have hF : 0 < 1 - cdf μ u := by
    rcases (sub_nonneg.mpr (cdf_le_one μ u)).lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at h1; linarith
  have hu0 : 0 < u := by
    have : 0 < u * f u / (1 - cdf μ u) := lt_of_lt_of_le hα₁ h1
    have : 0 < u * f u := by
      by_contra hc
      push_neg at hc
      have := div_nonpos_of_nonpos_of_nonneg hc hF.le
      linarith
    exact pos_of_mul_pos_left this hf.le
  exact ⟨hF, hu0⟩

/-- Derivative of `(1 - F u) * u ^ α` on the interior of `[t₀, ∞)`. -/
lemma hasDeriv_survival_pow (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α : ℝ)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (u : ℝ) (hu : u ∈ interior (Set.Ici t₀)) (hu0 : 0 < u) :
    HasDerivWithinAt (fun u => (1 - cdf μ u) * u ^ α)
      ((0 - f u) * u ^ α + (1 - cdf μ u) * (α * u ^ (α - 1))) (interior (Set.Ici t₀)) u := by
  rw [interior_Ici] at hu
  have hd : HasDerivWithinAt (cdf μ) (f u) (interior (Set.Ici t₀)) u :=
    (hdens u (le_of_lt hu)).1.mono interior_subset
  exact ((hasDerivWithinAt_const u _ (1 : ℝ)).sub hd).mul
    (Real.hasDerivAt_rpow_const (Or.inl hu0.ne')).hasDerivWithinAt

lemma survival_pow_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂) :
    AntitoneOn (fun u => (1 - cdf μ u) * u ^ α₁) (Set.Ici t₀) := by
  have hb := hazard_basic6 μ f t₀ α₁ α₂ hα₁ hdens hbounds
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici t₀) ?_
    (fun u hu => hasDeriv_survival_pow μ f t₀ α₁ hdens u hu
      (hb u (interior_subset hu)).2) ?_
  · apply ContinuousOn.mul
    · exact continuousOn_const.sub (fun u hu => (hdens u hu).1.continuousWithinAt)
    · apply ContinuousOn.rpow_const continuousOn_id
      intro u hu
      exact Or.inl (hb u hu).2.ne'
  · intro u hu
    have hu' : t₀ ≤ u := interior_subset hu
    obtain ⟨hF, hu0⟩ := hb u hu'
    have key : α₁ * (1 - cdf μ u) ≤ u * f u := by
      have := (hbounds u hu').1
      rwa [le_div_iff₀ hF] at this
    have hpow : 0 < u ^ (α₁ - 1) := Real.rpow_pos_of_pos hu0 _
    have heq : u ^ α₁ = u ^ (α₁ - 1) * u := by
      rw [Real.rpow_sub_one hu0.ne']; field_simp
    calc (0 - f u) * u ^ α₁ + (1 - cdf μ u) * (α₁ * u ^ (α₁ - 1))
        = u ^ (α₁ - 1) * (α₁ * (1 - cdf μ u) - u * f u) := by rw [heq]; ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpow.le (by linarith)

lemma survival_pow_monotone (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂) :
    MonotoneOn (fun u => (1 - cdf μ u) * u ^ α₂) (Set.Ici t₀) := by
  have hb := hazard_basic6 μ f t₀ α₁ α₂ hα₁ hdens hbounds
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici t₀) ?_
    (fun u hu => hasDeriv_survival_pow μ f t₀ α₂ hdens u hu
      (hb u (interior_subset hu)).2) ?_
  · apply ContinuousOn.mul
    · exact continuousOn_const.sub (fun u hu => (hdens u hu).1.continuousWithinAt)
    · apply ContinuousOn.rpow_const continuousOn_id
      intro u hu
      exact Or.inl (hb u hu).2.ne'
  · intro u hu
    have hu' : t₀ ≤ u := interior_subset hu
    obtain ⟨hF, hu0⟩ := hb u hu'
    have key : u * f u ≤ α₂ * (1 - cdf μ u) := by
      have := (hbounds u hu').2
      rwa [div_le_iff₀ hF] at this
    have hpow : 0 < u ^ (α₂ - 1) := Real.rpow_pos_of_pos hu0 _
    have heq : u ^ α₂ = u ^ (α₂ - 1) * u := by
      rw [Real.rpow_sub_one hu0.ne']; field_simp
    calc (0 : ℝ) ≤ u ^ (α₂ - 1) * (α₂ * (1 - cdf μ u) - u * f u) :=
          mul_nonneg hpow.le (by linarith)
      _ = (0 - f u) * u ^ α₂ + (1 - cdf μ u) * (α₂ * u ^ (α₂ - 1)) := by rw [heq]; ring

/-- `μ (Ioi t)` in real terms. -/
lemma real_Ioi (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (μ (Set.Ioi t)).toReal = 1 - cdf μ t := by
  have h1 : μ (Set.Ioi t) = 1 - ENNReal.ofReal (cdf μ t) := by
    rw [ofReal_cdf, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
  rw [h1, ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.mpr (cdf_le_one μ t)) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofReal (cdf_nonneg μ t)]

lemma real_Ioc (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ) (hab : a ≤ b) :
    (μ (Set.Ioc a b)).toReal = cdf μ b - cdf μ a := by
  have := StieltjesFunction.measure_Ioc (cdf μ) a b
  rw [measure_cdf] at this
  rw [this, ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_cdf μ hab))]

theorem theorem_6_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂) :
    ∀ t ≥ t₀, ∀ x : ℝ,
      GammaLaw α₁ x ≤ residualLife μ t (x * t) ∧ residualLife μ t (x * t) ≤ GammaLaw α₂ x := by
  intro t ht x
  have hb := hazard_basic6 μ f t₀ α₁ α₂ hα₁ hdens hbounds
  obtain ⟨hFt, ht0⟩ := hb t ht
  rcases lt_or_ge x 0 with hx | hx
  · have hempty : Set.Ioc t (t + x * t) = ∅ := Set.Ioc_eq_empty (by nlinarith)
    simp [residualLife, GammaLaw, hempty, hx.not_ge]
  · set b := (1 + x) * t with hb_def
    have htb : t ≤ b := by nlinarith
    have hbt0 : t₀ ≤ b := ht.trans htb
    obtain ⟨hFb, hb0⟩ := hb b hbt0
    have hres : residualLife μ t (x * t) = 1 - (1 - cdf μ b) / (1 - cdf μ t) := by
      have : t + x * t = b := by rw [hb_def]; ring
      rw [residualLife, this, real_Ioi, real_Ioc μ t b htb]
      field_simp
      ring
    have hx1 : 0 < 1 + x := by linarith
    have hA := survival_pow_antitone μ f t₀ α₁ α₂ hα₁ hdens hbounds ht hbt0 htb
    have hM := survival_pow_monotone μ f t₀ α₁ α₂ hα₁ hdens hbounds ht hbt0 htb
    simp only at hA hM
    rw [hb_def, Real.mul_rpow hx1.le ht0.le] at hA hM
    have hpow1 : 0 < t ^ α₁ := Real.rpow_pos_of_pos ht0 _
    have hpow2 : 0 < t ^ α₂ := Real.rpow_pos_of_pos ht0 _
    have hA' : (1 - cdf μ b) * (1 + x) ^ α₁ ≤ 1 - cdf μ t := by
      have : (1 - cdf μ b) * (1 + x) ^ α₁ * t ^ α₁ ≤ (1 - cdf μ t) * t ^ α₁ := by
        rw [mul_assoc]; exact hA
      exact le_of_mul_le_mul_right this hpow1
    have hM' : 1 - cdf μ t ≤ (1 - cdf μ b) * (1 + x) ^ α₂ := by
      have : (1 - cdf μ t) * t ^ α₂ ≤ (1 - cdf μ b) * (1 + x) ^ α₂ * t ^ α₂ := by
        rw [mul_assoc]; exact hM
      exact le_of_mul_le_mul_right this hpow2
    have hq1 : 0 < (1 + x) ^ α₁ := Real.rpow_pos_of_pos hx1 _
    have hq2 : 0 < (1 + x) ^ α₂ := Real.rpow_pos_of_pos hx1 _
    rw [hres, GammaLaw, GammaLaw, if_pos hx, if_pos hx, Real.rpow_neg hx1.le, Real.rpow_neg hx1.le]
    constructor
    · have : (1 - cdf μ b) / (1 - cdf μ t) ≤ ((1 + x) ^ α₁)⁻¹ := by
        rw [div_le_iff₀ hFt, inv_mul_eq_div, le_div_iff₀ hq1]
        exact hA'
      linarith
    · have : ((1 + x) ^ α₂)⁻¹ ≤ (1 - cdf μ b) / (1 - cdf μ t) := by
        rw [le_div_iff₀ hFt, inv_mul_eq_div, div_le_iff₀ hq2]
        exact hM'
      linarith

end BalkemaDeHaan.ParetoBounds

open BalkemaDeHaan.ParetoBounds


theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂) :
    ∀ t ≥ t₀, ∀ x : ℝ,
      GammaLaw α₁ x ≤ residualLife μ t (x * t) ∧ residualLife μ t (x * t) ≤ GammaLaw α₂ x := by
  exact theorem_6_core μ f t₀ α₁ α₂ hα₁ hα₂ hdens hbounds
