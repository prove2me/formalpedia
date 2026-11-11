-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys57_ae_finite_supported_random_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:42:12.135569+00:00
-- url     : https://prove2.me/submissions/94f7d821-55b1-4e3e-9960-af7156e6cfaa

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys56_uniform_finite_random_integral_strongly_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Localising random measures at finite mass gives a.e. measurable signed integrals. -/
theorem solution
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (M : Ω → Measure α)
    (hM : ∀ B : Set α, MeasurableSet B →
      Measurable (fun ω : Ω => M ω B))
    (S : Set α) (hS : MeasurableSet S)
    (f : Ω × α → ℝ) (hf : StronglyMeasurable f)
    (hfS : ∀ ω p, p ∉ S → f (ω, p) = 0)
    (hFinite : ∀ᵐ ω ∂P, M ω S < ⊤) :
    AEStronglyMeasurable
      (fun ω : Ω => ∫ p, f (ω, p) ∂M ω) P := by
  let G : ℕ → Ω → Measure α := fun n ω =>
    if M ω S < (n : ℝ≥0∞) then (M ω).restrict S else 0
  have hGmeas (n : ℕ) (B : Set α) (hB : MeasurableSet B) :
      Measurable (fun ω : Ω => G n ω B) := by
    have hSel : MeasurableSet {ω : Ω | M ω S < (n : ℝ≥0∞)} :=
      measurableSet_Iio.preimage (hM S hS)
    have hEval := hM (B ∩ S) (hB.inter hS)
    have hi : Measurable (fun ω : Ω =>
        if M ω S < (n : ℝ≥0∞) then M ω (B ∩ S) else 0) :=
      hEval.ite hSel measurable_const
    convert hi using 1
    funext ω
    by_cases h : M ω S < (n : ℝ≥0∞)
    · simp only [G, if_pos h]
      exact Measure.restrict_apply hB
    · simp [G, h]
  have hGmass (n : ℕ) (ω : Ω) : G n ω Set.univ ≤ (n : ℝ≥0∞) := by
    by_cases h : M ω S < (n : ℝ≥0∞)
    · simpa only [G, if_pos h, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter] using h.le
    · simp [G, h]
  let F : ℕ → Ω → ℝ := fun n ω =>
    ∫ p, f (ω, p) ∂G n ω
  have hF (n : ℕ) : StronglyMeasurable (F n) := by
    exact avram_bvb_phys56_uniform_finite_random_integral_strongly_measurable
      (G n) (hGmeas n) (n : ℝ≥0∞) ENNReal.coe_lt_top
      (hGmass n) f hf
  have hRestrict (ω : Ω) :
      (∫ p, f (ω, p) ∂(M ω).restrict S) =
        ∫ p, f (ω, p) ∂M ω := by
    calc
      _ = ∫ p in S, f (ω, p) ∂M ω := rfl
      _ = ∫ p, S.indicator (fun p => f (ω, p)) p ∂M ω :=
        (integral_indicator hS).symm
      _ = ∫ p, f (ω, p) ∂M ω := by
        congr 1
        funext p
        by_cases hp : p ∈ S
        · simp [Set.indicator_of_mem hp]
        · simp [Set.indicator, hp, hfS ω p hp]
  apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun n => (hF n).aestronglyMeasurable)
  filter_upwards [hFinite] with ω hω
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_of_lt hω)
  have hev : ∀ᶠ m : ℕ in Filter.atTop,
      F m ω = (∫ p, f (ω, p) ∂M ω) := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hnm
    have hm : M ω S < (m : ℝ≥0∞) :=
      lt_of_lt_of_le hn (by exact_mod_cast hnm)
    simpa only [F, G, if_pos hm] using hRestrict ω
  have hconst : Tendsto (fun _ : ℕ =>
      ∫ p, f (ω, p) ∂M ω) Filter.atTop
      (nhds (∫ p, f (ω, p) ∂M ω)) := tendsto_const_nhds
  -- The finite-mass localisation is eventually the original restricted measure.
  have hev' : (fun _ : ℕ => ∫ p, f (ω, p) ∂M ω)
      =ᶠ[Filter.atTop] (fun m => F m ω) := by
    filter_upwards [hev] with m hm
    exact hm.symm
  exact hconst.congr' hev'
