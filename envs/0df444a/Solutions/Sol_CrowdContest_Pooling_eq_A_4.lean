-- Prove2me | solution 1 for CrowdContest.Pooling.eq_A_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:10:54.263758+00:00
-- url     : https://prove2.me/submissions/f9fcefdd-29d7-405d-8fc0-6cead28002cb

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density

open MeasureTheory

open CrowdContest.Pooling

theorem solution (φ : ℝ → ℝ) (hφ : IsDensity φ) (hmean : Integrable (fun x => x * φ x))
    (n : ℕ) (hn : 1 ≤ n) :
    expMax φ n = ∫ u in (0 : ℝ)..1, quantile (cdf φ) u * (n : ℝ) * u ^ (n - 1) := by
  obtain ⟨hmeas, hnn, hint1⟩ := hφ
  have hint : Integrable φ := by
    by_contra h
    rw [integral_undef h] at hint1
    norm_num at hint1
  set F := cdf φ with hFdef
  let f : ℝ → NNReal := fun x => (φ x).toNNReal
  have hf : Measurable f := hmeas.real_toNNReal
  let μ : Measure ℝ := volume.withDensity (fun x => (f x : ENNReal))
  have hF0 : ∀ x, 0 ≤ F x := fun x => setIntegral_nonneg measurableSet_Iic (fun t _ => hnn t)
  have hμset : ∀ s, MeasurableSet s → μ s = ENNReal.ofReal (∫ t in s, φ t) := by
    intro s hs
    rw [withDensity_apply _ hs, ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (Filter.Eventually.of_forall (fun t => hnn t))]
    rfl
  have hμIic : ∀ x, μ (Set.Iic x) = ENNReal.ofReal (F x) := fun x => hμset _ measurableSet_Iic
  have hμuniv : μ Set.univ = 1 := by
    rw [hμset _ MeasurableSet.univ, Measure.restrict_univ, hint1, ENNReal.ofReal_one]
  haveI : IsProbabilityMeasure μ := ⟨hμuniv⟩
  have hFcdf : F = ProbabilityTheory.cdf μ := by
    funext x
    have h := ProbabilityTheory.ofReal_cdf μ x
    rw [hμIic] at h
    exact ((ENNReal.ofReal_eq_ofReal_iff (ProbabilityTheory.cdf_nonneg μ x) (hF0 x)).1 h).symm
  have hmono : Monotone F := hFcdf ▸ ProbabilityTheory.monotone_cdf μ
  have hbot : Filter.Tendsto F Filter.atBot (nhds 0) := hFcdf ▸ ProbabilityTheory.tendsto_cdf_atBot μ
  have htop : Filter.Tendsto F Filter.atTop (nhds 1) := hFcdf ▸ ProbabilityTheory.tendsto_cdf_atTop μ
  have hcont : Continuous F := by
    have h1 : ∀ x, F x = F 0 + ∫ t in (0 : ℝ)..x, φ t := by
      intro x
      have := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (f := φ) (a := 0) (b := x)
        hint.integrableOn hint.integrableOn
      simp only [hFdef, cdf] at this ⊢
      linarith
    have h2 : Continuous fun x => ∫ t in (0 : ℝ)..x, φ t :=
      intervalIntegral.continuous_primitive (fun a b => hint.intervalIntegrable) 0
    have : F = fun x => F 0 + ∫ t in (0 : ℝ)..x, φ t := funext h1
    rw [this]
    exact continuous_const.add h2
  set Q := quantile F with hQdef
  -- quantile facts
  have hQ : ∀ u ∈ Set.Ioo (0 : ℝ) 1, (∀ x, Q u ≤ x ↔ u ≤ F x) ∧ F (Q u) = u := by
    intro u hu
    obtain ⟨hu0, hu1⟩ := hu
    have hne : ({x | u ≤ F x} : Set ℝ).Nonempty := by
      obtain ⟨x, hx⟩ := ((tendsto_order.1 htop).1 u hu1).exists
      exact ⟨x, hx.le⟩
    obtain ⟨y, hy⟩ := Filter.eventually_atBot.1 ((tendsto_order.1 hbot).2 u hu0)
    have hbdd : BddBelow ({x | u ≤ F x} : Set ℝ) := by
      refine ⟨y, fun x hx => ?_⟩
      by_contra hxy
      push_neg at hxy
      have := hy x hxy.le
      simp only [Set.mem_setOf_eq] at hx
      linarith
    have hclosed : IsClosed ({x | u ≤ F x} : Set ℝ) := isClosed_le continuous_const hcont
    have hmem : u ≤ F (Q u) := hclosed.csInf_mem hne hbdd
    have hiff : ∀ x, Q u ≤ x ↔ u ≤ F x := by
      intro x
      constructor
      · intro hx; exact le_trans hmem (hmono hx)
      · intro hx; exact csInf_le hbdd hx
    refine ⟨hiff, le_antisymm ?_ hmem⟩
    have hyQ : y ≤ Q u := by
      by_contra h
      push_neg at h
      have := hy (Q u) h.le
      linarith
    have hIVT := intermediate_value_Icc hyQ hcont.continuousOn
    have hyu : u ∈ Set.Icc (F y) (F (Q u)) := ⟨(hy y le_rfl).le, hmem⟩
    obtain ⟨z, hz, hFz⟩ := hIVT hyu
    have hQz : Q u ≤ z := (hiff z).2 hFz.ge
    have : z = Q u := le_antisymm hz.2 hQz
    rw [← this, hFz]
  have hQmono : MonotoneOn Q (Set.Ioo (0 : ℝ) 1) := by
    intro u hu v hv huv
    rw [(hQ u hu).1]
    rw [(hQ v hv).2]
    exact huv
  have hQae : AEMeasurable Q (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hQmono
  set ν : Measure ℝ := (volume.restrict (Set.Ioo (0 : ℝ) 1)).map Q with hν
  have hνIic : ∀ x, μ (Set.Iic x) = ν (Set.Iic x) := by
    intro x
    rw [hμIic, hν, Measure.map_apply_of_aemeasurable hQae measurableSet_Iic,
      Measure.restrict_apply' measurableSet_Ioo]
    have hset : Q ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 = Set.Ioo 0 1 ∩ Set.Iic (F x) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, ((hQ u h2).1 x).1 h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨((hQ u h1).1 x).2 h2, h1⟩
    rw [hset]
    have hF1 : F x ≤ 1 := hFcdf ▸ ProbabilityTheory.cdf_le_one μ x
    rcases hF1.lt_or_eq with hlt | heq
    · have : Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (F x) = Set.Ioc 0 (F x) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
      rw [this, Real.volume_Ioc, sub_zero]
    · have : Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (F x) = Set.Ioo 0 1 := by
        rw [heq]
        exact Set.inter_eq_left.2 (fun u hu => le_of_lt hu.2)
      rw [this, Real.volume_Ioo, heq, sub_zero]
  have hμν : μ = ν := Measure.ext_of_Iic μ ν hνIic
  -- the integrand
  let g : ℝ → ℝ := fun ξ => ξ * (n : ℝ) * F ξ ^ (n - 1)
  have hgc : Continuous g := by
    exact (continuous_id.mul continuous_const).mul (hcont.pow _)
  have h1 : expMax φ n = ∫ ξ, g ξ ∂μ := by
    rw [integral_withDensity_eq_integral_smul hf]
    unfold expMax
    congr 1
    funext ξ
    simp only [g, f, NNReal.smul_def, Real.coe_toNNReal _ (hnn ξ), smul_eq_mul]
    ring
  rw [h1, hμν, hν, integral_map hQae hgc.aestronglyMeasurable,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
  simp only [g, (hQ u hu).2]
